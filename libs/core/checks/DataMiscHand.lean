import Lean.Elab.Command
-- add the library modules your rows need here (e.g. `import Init`, `import Std.Sat.AIG.CNF`); avoid `import Lean`/`import Std` (1.5 GB)
import Init

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

/-!
Hand pass `DataMisc` (hand22): 91 hypotheses of private theorems in `Init.Data` (Iterators: the
`Flatten` termination relations, the collectors' `go` lemmas, `flattenAfter`, `filterMapWithPostcondition`;
`Nat.Fold`, `Nat.ToString`, `Array`/`List`/`Vector`/`Fin`/`BitVec` helpers, `Int.DivMod`, `Order.Ord`)
and of `Init.While`, `Init.WFComputable`, `Init.Internal.Order.While`. For hypothesis `hᵢ` of `T` each
declaration proves `¬T'` (`drop0%`, universes `0`), `¬∀ indep, Hᵢ` (`indep0%`, or `indepu%` with chosen
universes) or `T'` (`drop%`/`indep%`).

72 necessary, 10 removable, 9 independent (opaque fixpoint; `runs/hand22/DataMisc_independent.jsonl`,
support lemmas `*_neg` in the last section).

Removable: `clz.log2Aux_eq` (`n ≠ 0`: for `n = 0` the search keeps `lo = 0`), `neg_udiv_…` (both msb
hypotheses: the library proof never uses them), `toInt_signExtend_of_lt` (`w < v`: the public
`toInt_signExtend_of_le`), `two_pow_dvd_mul_mod` (`s ≤ w`: otherwise the remainder is `0`),
`Int.ediv_ediv_of_pos` (`0 < z`: `ediv_ediv_of_nonneg`), `addRecAux_append_extractLsb'` (`hcast`
follows from `0 < len`), `toList_reverse.go` (`as.size = xs.size` follows from `H`), `fixGraph_fixC`
(`Acc r x` follows from `WellFounded r`), `minIdxOn_eq_go_drop` (`IsLinearPreorder`: the scan and the
fold make the same comparisons for any `LE`; the library proof with `minOn_append` replaced by
`foldl_append`).

Reusable models (namespace `DataMiscHand`):
* `Rps` (rock-paper-scissors `≤` on `Nat`, from `OrderListHand`), `R1` on `Bool` (`false` accessible,
  `true` not; `not_acc_R1_true`, `not_wf_R1`), `CB` (`Nat × α`, `bind` adds `1`, default `map`), `LWr`
  (lawful `Nat` writer), `minIdxGo_nil`/`minIdxGo_cons` (equations of the private `minIdxOn.go`).
* Iterators: `LP β` (skips to itself; `LP.not_finite`, `LP.not_productive`, from `OpABHand`), `S1 β`
  (state `true` skips to `false`, which is done; `Finite`, with `S1.skip` for the `rel_of_skip`
  premises), `YC` (yields `0` forever, each step counts `1` in `LN`; with `no_descent`), `wf_irrefl`.
* Monads: `MW` (`map` adds 1), `BW` (`bind` adds 1), `AW` (lawful, `attach` adds 1), from
  `ItMonadMBHand`; `LN` (lawful writer with `Nat` counts).
* Evaluation (law-free): `go_eq'`, `revgo_eq'`, `step_flattenAfter'`, `step_mwp`, `step_fmwp`, the
  tactics `ev`/`evh` (from `ItMonadMBHand`); `FA%` is the private `Std.IterM.flattenAfter`.
Private definitions are unfolded with their `eq_def` lemmas through `priv%`
(`Array.insertIdx.loop`, `Array.findFinIdx?.loop`).

Run with `runs/hand22/lean.sh checks/DataMiscHand.lean`.
-/

/-- `indepu% [l₁, …] T i`: `indep% T i` with `T`'s universe parameters set to the given levels (for refutations). -/
elab "indepu% " "[" ls:num,* "]" T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := (ls.getElems.map fun l => Level.ofNat l.getNat).toList
  unless us.length == ci.levelParams.length do throwError "wrong number of universe levels"
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



namespace DataMiscHand

-- `Array.getElem_shrink_loop`
theorem Array.getElem_shrink_loop.h4 : ¬ indep0% _private.Init.Data.Array.Lemmas.«0».Array.getElem_shrink_loop 4 := fun h => by
  have := h (α := Nat) (xs := #[]) (n := 0) (i := 0)
  exact absurd this (by decide)

-- `Array.toList_reverse.go`
theorem Array.toList_reverse.go.h6 : ¬ drop0% _private.Init.Data.Array.Lemmas.«0».Array.toList_reverse.go 6 := fun h => by
  have := h (xs := #[0, 1]) #[0, 0] 0 0 (by decide) rfl (by intro k; match k with | 0 => rfl | 1 => rfl | k+2 => simp) 0
  rw [Array.reverse.loop] at this
  simp at this

-- `Array.toList_reverse.go`
theorem Array.toList_reverse.go.h7 : drop% _private.Init.Data.Array.Lemmas.«0».Array.toList_reverse.go 7 := by
  intro α xs as i j hj h H k
  have key : ∀ k, as.size ≤ k ↔ xs.size ≤ k := by
    intro k
    have e1 : as.toList[k]? = none ↔ as.size ≤ k := by simp
    have e2 : (if i ≤ k ∧ k ≤ j then xs.toList[k]? else xs.toList.reverse[k]?) = none ↔ xs.size ≤ k := by
      split <;> simp
    rw [← e1, ← e2, H k]
  have h₂ : as.size = xs.size := by
    have a := (key as.size).1 (Nat.le_refl _)
    have b := (key xs.size).2 (Nat.le_refl _)
    omega
  exact (priv% _private.Init.Data.Array.Lemmas.«0».Array.toList_reverse.go) as i j hj h h₂ H k

-- `Array.mapFinIdx_induction.go`
theorem Array.mapFinIdx_induction.go.h10 : ¬ indep0% _private.Init.Data.Array.MapIdx.«0».Array.mapFinIdx_induction.go 10 := fun h => by
  have := h (α := Nat) (β := Nat) #[] (fun _ _ _ => 0) (fun _ => True) (fun _ _ _ => True)
    (fun _ h _ => absurd h (Nat.not_lt_zero _)) (bs := #[]) (i := 1) (j := 0) rfl (fun _ h _ => absurd h (Nat.not_lt_zero _)) trivial
  exact absurd this (by decide)

-- `Array.mapFinIdx_induction.go`
theorem Array.mapFinIdx_induction.go.h11 : ¬ drop0% _private.Init.Data.Array.MapIdx.«0».Array.mapFinIdx_induction.go 11 := fun h => by
  have := h (α := Nat) (β := Nat) #[] (fun _ _ _ => 0) (fun _ => True) (fun _ _ _ => True)
    (fun _ h _ => absurd h (Nat.not_lt_zero _)) (bs := #[0]) (i := 0) (j := 0) (h := rfl) (fun _ h _ => absurd h (Nat.not_lt_zero _)) trivial
  obtain ⟨-, eq, -⟩ := this
  exact absurd eq (by decide)

-- `Array.mapFinIdx_induction.go`
theorem Array.mapFinIdx_induction.go.h12 : ¬ drop0% _private.Init.Data.Array.MapIdx.«0».Array.mapFinIdx_induction.go 12 := fun h => by
  have := h (α := Nat) (β := Nat) #[0] (fun _ _ _ => 1) (fun _ => True) (fun _ b _ => b = 1)
    (fun _ _ _ => ⟨rfl, trivial⟩) (bs := #[0]) (i := 0) (j := 1) (h := rfl) rfl trivial
  obtain ⟨-, eq, H⟩ := this
  have h0 := H 0 (by decide)
  simp [Array.mapFinIdxM.map] at h0

-- `List.mapFinIdxM_toArray.go`
theorem List.mapFinIdxM_toArray.go.h9 : ¬ indep0% _private.Init.Data.Array.MapIdx.«0».List.mapFinIdxM_toArray.go 9 := fun h => by
  have := h (m := Id) (α := Nat) (β := Nat) (l := []) (f := fun _ _ _ => (0 : Nat)) 1 #[]
  exact absurd this (by decide)

-- `Vector.toArray_mapFinIdxM.go`
theorem Vector.toArray_mapFinIdxM.go.h10 : ¬ indep0% _private.Init.Data.Vector.MapIdx.«0».Vector.toArray_mapFinIdxM.go 10 := fun h => by
  have := h (m := Id) (α := Nat) (n := 0) (β := Nat) (xs := #v[]) (f := fun _ _ _ => (0 : Nat)) 1 0 #v[]
  exact absurd this (by decide)

theorem log2Aux_zero : ∀ fuel hi, BitVec.clz.log2Aux fuel 0 hi 0 = 0
  | 0, _ => rfl
  | fuel + 1, hi => by
    rw [BitVec.clz.log2Aux]
    split
    · rfl
    · simp [log2Aux_zero fuel]

-- `BitVec.clz.log2Aux_eq`
theorem BitVec.clz.log2Aux_eq.h4 : drop% _private.Init.Data.BitVec.Basic.«0».BitVec.clz.log2Aux_eq 4 := by
  intro fuel lo hi n hlo hhi hf
  by_cases hn : n = 0
  · subst hn
    have : lo = 0 := by simp at hlo; omega
    subst this
    simpa using log2Aux_zero fuel hi
  · exact (priv% _private.Init.Data.BitVec.Basic.«0».BitVec.clz.log2Aux_eq) hn hlo hhi hf

-- `BitVec.addRecAux_append_extractLsb'`
theorem BitVec.addRecAux_append_extractLsb'.h2 : indep% _private.Init.Data.BitVec.Bitblast.«0».BitVec.addRecAux_append_extractLsb' 2 := by
  intro len w x hlen
  cases len with
  | zero => omega
  | succ len => simp [Nat.succ_mul, Nat.add_comm]

theorem negUdiv {w : Nat} {x y : BitVec w} :
    -x / y = BitVec.intMin w ↔ (x = BitVec.intMin w ∧ y = 1#w) := by
  constructor
  · intro h
    rcases w with _ | w; decide +revert
    have : (-x / y).msb = true := by simp [h, BitVec.msb_intMin]
    rw [BitVec.msb_udiv] at this
    simp only [bool_to_prop] at this
    obtain ⟨hx, hy⟩ := this
    simp only [beq_iff_eq] at hy
    subst hy
    simp only [BitVec.udiv_one, BitVec.neg_eq_intMin] at h
    simp [h]
  · rintro ⟨hx, hy⟩
    subst hx hy
    simp

-- `BitVec.neg_udiv_eq_intMin_iff_eq_intMin_eq_one_of_msb_eq_true`
theorem BitVec.neg_udiv_eq_intMin_iff_eq_intMin_eq_one_of_msb_eq_true.h3 : drop% _private.Init.Data.BitVec.Bitblast.«0».BitVec.neg_udiv_eq_intMin_iff_eq_intMin_eq_one_of_msb_eq_true 3 :=
  fun _ => negUdiv

-- `BitVec.neg_udiv_eq_intMin_iff_eq_intMin_eq_one_of_msb_eq_true`
theorem BitVec.neg_udiv_eq_intMin_iff_eq_intMin_eq_one_of_msb_eq_true.h4 : drop% _private.Init.Data.BitVec.Bitblast.«0».BitVec.neg_udiv_eq_intMin_iff_eq_intMin_eq_one_of_msb_eq_true 4 :=
  fun _ => negUdiv

-- `BitVec.toInt_signExtend_of_le.toInt_signExtend_of_lt`
theorem BitVec.toInt_signExtend_of_lt.h4 : drop% _private.Init.Data.BitVec.Lemmas.«0».BitVec.toInt_signExtend_of_le.toInt_signExtend_of_lt 4 := by
  intro w v h x
  exact BitVec.toInt_signExtend_of_le h

-- `BitVec.two_pow_dvd_mul_mod`
theorem BitVec.two_pow_dvd_mul_mod.h3 : drop% _private.Init.Data.BitVec.Lemmas.«0».BitVec.two_pow_dvd_mul_mod 3 := by
  intro a s w
  by_cases hs : s ≤ w
  · exact (priv% _private.Init.Data.BitVec.Lemmas.«0».BitVec.two_pow_dvd_mul_mod) hs
  · have : 2 ^ w ∣ a * 2 ^ s := Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) (Nat.dvd_mul_left _ _)
    rw [Nat.mod_eq_zero_of_dvd this]
    exact Nat.dvd_zero _

-- `Fin.hIterateFrom_elim`
theorem Fin.hIterateFrom_elim.h5 : ¬ indep0% _private.Init.Data.Fin.Iterate.«0».Fin.hIterateFrom_elim 5 := fun h => by
  have := h (P := fun _ => True) (fun _ _ => True) (n := 0) (fun i => i.elim0) (i := 1) trivial trivial (fun k => k.elim0)
  exact absurd this (by decide)

-- `Fin.reverseInduction_castSucc_aux`
theorem Fin.reverseInduction_castSucc_aux.h5 : ¬ indep0% _private.Init.Data.Fin.Lemmas.«0».Fin.reverseInduction_castSucc_aux 5 := fun h => by
  have := h (n := 1) (motive := fun _ => True) (succ := fun _ _ => trivial) 0 5 (by decide)
  exact absurd this (by decide)

-- `Fin.reverseInduction_castSucc_aux`
theorem Fin.reverseInduction_castSucc_aux.h6 : ¬ indep0% _private.Init.Data.Fin.Lemmas.«0».Fin.reverseInduction_castSucc_aux 6 := fun h => by
  have := h (n := 1) (motive := fun _ => True) (succ := fun _ _ => trivial) 0 0 (by decide) trivial
  exact absurd this (by decide)

-- `Int.ediv_ediv_of_pos`
theorem Int.ediv_ediv_of_pos.h4 : drop% _private.Init.Data.Int.DivMod.Lemmas.«0».Int.ediv_ediv_of_pos 4 := by
  intro x y z hy
  exact Int.ediv_ediv_of_nonneg (Int.le_of_lt hy)

-- `Nat.allTR_loop_congr`
theorem Nat.allTR_loop_congr.h2 : ¬ indep0% _private.Init.Data.Nat.Fold.«0».Nat.allTR_loop_congr 2 := fun h => by
  have := h (n := 0) (m := 1) (fun _ _ => true) 0 (Nat.le_refl _)
  exact absurd this (by decide)

-- `Nat.allTR_loop_congr`
theorem Nat.allTR_loop_congr.h5 : ¬ indep0% _private.Init.Data.Nat.Fold.«0».Nat.allTR_loop_congr 5 := fun h => by
  have := h (n := 0) (m := 0) rfl (fun _ _ => true) 1
  exact absurd this (by decide)

-- `Nat.anyTR_loop_congr`
theorem Nat.anyTR_loop_congr.h2 : ¬ indep0% _private.Init.Data.Nat.Fold.«0».Nat.anyTR_loop_congr 2 := fun h => by
  have := h (n := 0) (m := 1) (fun _ _ => true) 0 (Nat.le_refl _)
  exact absurd this (by decide)

-- `Nat.anyTR_loop_congr`
theorem Nat.anyTR_loop_congr.h5 : ¬ indep0% _private.Init.Data.Nat.Fold.«0».Nat.anyTR_loop_congr 5 := fun h => by
  have := h (n := 0) (m := 0) rfl (fun _ _ => true) 1
  exact absurd this (by decide)

-- `Nat.foldTR_loop_congr`
theorem Nat.foldTR_loop_congr.h3 : ¬ indep0% _private.Init.Data.Nat.Fold.«0».Nat.foldTR_loop_congr 3 := fun h => by
  have := h (α := Nat) (n := 0) (m := 1) (fun _ _ a => a) 0 (Nat.le_refl _) 0
  exact absurd this (by decide)

-- `Nat.foldTR_loop_congr`
theorem Nat.foldTR_loop_congr.h6 : ¬ indep0% _private.Init.Data.Nat.Fold.«0».Nat.foldTR_loop_congr 6 := fun h => by
  have := h (α := Nat) (n := 0) (m := 0) rfl (fun _ _ a => a) 1 0
  exact absurd this (by decide)

-- `Nat.allLTTR_loop_eq_true`
theorem Nat.allLTTR_loop_eq_true.h3 : ¬ indep0% _private.Init.Data.Nat.Lemmas.«0».Nat.allLTTR_loop_eq_true 3 := fun h => by
  have := h (n := 0) (f := fun _ _ => true) 1
  exact absurd this (by decide)

-- `Nat.anyLTTR_loop_eq_true`
theorem Nat.anyLTTR_loop_eq_true.h3 : ¬ indep0% _private.Init.Data.Nat.Lemmas.«0».Nat.anyLTTR_loop_eq_true 3 := fun h => by
  have := h (n := 0) (f := fun _ _ => true) 1
  exact absurd this (by decide)

-- `Nat.apply_dfoldCast`
theorem Nat.apply_dfoldCast.h5 : ¬ indep0% _private.Init.Data.Nat.Fold.«0».Nat.apply_dfoldCast 5 := fun h => by
  have := h (n := 0) (α := fun _ _ => Unit) (fun _ h _ => absurd h (Nat.not_lt_zero _)) (i := 0) (j := 0) (w := rfl)
  exact absurd this (by decide)

-- `Nat.apply_dfoldCast`
theorem Nat.apply_dfoldCast.h6 : ¬ indep0% _private.Init.Data.Nat.Fold.«0».Nat.apply_dfoldCast 6 := fun h => by
  have := h (n := 1) (α := fun _ _ => Unit) (fun _ _ _ => ()) (i := 0) (j := 1) (by decide)
  exact absurd this (by decide)

-- `Nat.dfoldCast_rfl`
theorem Nat.dfoldCast_rfl.h3 : ¬ indep0% _private.Init.Data.Nat.Fold.«0».Nat.dfoldCast_rfl 3 := fun h => by
  have := h (i := 1) (n := 0) (α := fun _ _ => Unit) rfl
  exact absurd this (by decide)

-- `Nat.dfoldCast_trans`
theorem Nat.dfoldCast_trans.h5 : ¬ indep0% _private.Init.Data.Nat.Fold.«0».Nat.dfoldCast_trans 5 := fun h => by
  have := h (i := 1) (n := 0) (j := 1) (k := 1) (α := fun _ _ => Unit) rfl rfl
  exact absurd this (by decide)

-- `Nat.dfoldCast_trans`
theorem Nat.dfoldCast_trans.h6 : ¬ indep0% _private.Init.Data.Nat.Fold.«0».Nat.dfoldCast_trans 6 := fun h => by
  have := h (i := 0) (n := 0) (j := 1) (k := 1) (α := fun _ _ => Unit) (Nat.le_refl _) rfl ()
  exact absurd this (by decide)

-- `Nat.dfoldCast_trans`
theorem Nat.dfoldCast_trans.h7 : ¬ indep0% _private.Init.Data.Nat.Fold.«0».Nat.dfoldCast_trans 7 := fun h => by
  have := h (i := 0) (n := 0) (j := 0) (k := 1) (α := fun _ _ => Unit) (Nat.le_refl _) rfl ()
  exact absurd this (by decide)

-- `Nat.dfold_loop_succ`
theorem Nat.dfold_loop_succ.h5 : ¬ indep0% _private.Init.Data.Nat.Fold.«0».Nat.dfold_loop_succ 5 := fun h => by
  have := h (n := 0) (j := 1) (α := fun _ _ => Unit) (fun _ _ _ => ()) ()
  exact absurd this (by decide)

-- `List.pmap_eq_pmapImpl.go`
theorem List.pmap_eq_pmapImpl.go.h5 : ¬ indep0% _private.Init.Data.List.Attach.«0».List.pmap_eq_pmapImpl.go 5 := fun h => by
  exact h Nat Nat (fun _ => False) (fun _ h => h.elim) [0] (List.mem_singleton_self 0)

-- `List.combineMinIdxOn_assoc`
theorem List.combineMinIdxOn_assoc.h16 : ¬ indep0% _private.Init.Data.List.MinMaxIdx.«0».List.combineMinIdxOn_assoc 16 := fun h => by
  have := h (β := Nat) (α := Nat) (xys := []) (xs := [0]) (ys := [0]) (zs := [0]) (i := 0) (j := 0) (k := 0) (f := id)
    (by decide) (by decide) (by decide)
  exact absurd this (by decide)

-- `Nat.toDigitsCore_toDigitsCore`
theorem Nat.toDigitsCore_toDigitsCore.h10 : ¬ drop0% _private.Init.Data.Nat.ToString.«0».Nat.toDigitsCore_toDigitsCore 10 := fun h => by
  have := h (b := 2) (n := 1) (d := 0) (fuel := 0) (nf := 2) (df := 1) (cs := []) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact absurd this (by decide)

-- `Nat.toDigitsCore_toDigitsCore`
theorem Nat.toDigitsCore_toDigitsCore.h11 : ¬ drop0% _private.Init.Data.Nat.ToString.«0».Nat.toDigitsCore_toDigitsCore 11 := fun h => by
  have := h (b := 2) (n := 1) (d := 0) (fuel := 5) (nf := 0) (df := 1) (cs := []) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact absurd this (by decide)

-- `Nat.toDigitsCore_toDigitsCore`
theorem Nat.toDigitsCore_toDigitsCore.h12 : ¬ drop0% _private.Init.Data.Nat.ToString.«0».Nat.toDigitsCore_toDigitsCore 12 := fun h => by
  have := h (b := 2) (n := 1) (d := 0) (fuel := 5) (nf := 2) (df := 0) (cs := []) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact absurd this (by decide)

-- `Std.Iter.forIn'_toList.aux`
theorem Iter.forIn'_toList.aux.h11 : ¬ indep0% _private.Init.Data.Iterators.Lemmas.Consumers.Loop.«0».Std.Iter.forIn'_toList.aux 11 := fun h => by
  have := h (ρ := List Nat) (α := Nat) (γ := Nat) (m := Id) (r := []) (s := [0]) (init := 0) (f := fun _ _ c => pure (.done c))
  exact absurd this (by decide)

-- `List.insertIdx_loop_toArray`
theorem List.insertIdx_loop_toArray.h5 : ¬ drop0% _private.Init.Data.List.ToArray.«0».List.insertIdx_loop_toArray 5 := fun h => by
  have := h (α := Nat) 1 [0] 0 (by decide)
  have := congrArg Array.size this
  rw [(priv% _private.Init.Data.Array.Basic.«0».Array.insertIdx.loop.eq_def)] at this
  simp at this

-- `List.findFinIdx?_loop_toArray`
theorem List.findFinIdx?_loop_toArray.h6 : ¬ drop0% _private.Init.Data.List.ToArray.«0».List.findFinIdx?_loop_toArray 6 := fun hT => by
  have := @hT Nat [0] (fun n => n % 2 == 0) 0 [1] rfl
  rw [(priv% _private.Init.Data.Array.Basic.«0».Array.findFinIdx?.loop.eq_def), (priv% _private.Init.Data.Array.Basic.«0».Array.findFinIdx?.loop.eq_def)] at this
  simp [List.findFinIdx?.go] at this

/-- `Nat` with rock-paper-scissors `≤` (`a ≤ b ↔ b ≡ a ∨ b ≡ a + 1 (mod 3)`): reflexive and total,
not transitive (from `OrderListHand`). -/
def Rps := Nat
instance : OfNat Rps n := ⟨(n : Nat)⟩
instance : DecidableEq Rps := inferInstanceAs (DecidableEq Nat)
def Rps.val (a : Rps) : Nat := a
instance : LE Rps := ⟨fun a b => b.val % 3 = a.val % 3 ∨ b.val % 3 = (a.val + 1) % 3⟩
instance : DecidableLE Rps := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

-- `List.combineMinIdxOn_assoc`
theorem List.combineMinIdxOn_assoc.h5 : ¬ drop0% _private.Init.Data.List.MinMaxIdx.«0».List.combineMinIdxOn_assoc 5 := fun h => by
  have := h (β := Rps) (α := Rps) (xys := [0, 1]) (xs := [0]) (ys := [1]) (zs := [2]) (i := 0) (j := 0) (k := 0) (f := id)
    (by decide) (by decide) (by decide) rfl
  exact absurd this (by decide)

-- `List.minIdxOn_cons_aux`
theorem List.minIdxOn_cons_aux.h4 : ¬ drop0% _private.Init.Data.List.MinMaxIdx.«0».List.minIdxOn_cons_aux 4 := fun h => by
  have := h (β := Rps) (α := Rps) (x := 0) (xs := [2, 1]) (f := id) (by simp)
  exact absurd this (by decide)

-- `List.minIdxOn_append_aux`
theorem List.minIdxOn_append_aux.h4 : ¬ drop0% _private.Init.Data.List.MinMaxIdx.«0».List.minIdxOn_append_aux 4 := fun h => by
  have := h (β := Rps) (α := Rps) (xs := [0]) (ys := [2, 1]) (f := id) (by simp) (by simp)
  exact absurd this (by decide)

theorem minIdxGo_nil {β α : Type _} [LE β] [DecidableLE β] (f : α → β) (x : α) (i j : Nat) :
    (priv% _private.Init.Data.List.MinMaxIdx.«0».List.minIdxOn.go) f x i j [] = i := rfl

theorem minIdxGo_cons {β α : Type _} [LE β] [DecidableLE β] (f : α → β) (x : α) (i j : Nat) (y : α) (ys : List α) :
    (priv% _private.Init.Data.List.MinMaxIdx.«0».List.minIdxOn.go) f x i j (y :: ys) =
      if f x ≤ f y then (priv% _private.Init.Data.List.MinMaxIdx.«0».List.minIdxOn.go) f x i (j + 1) ys
      else (priv% _private.Init.Data.List.MinMaxIdx.«0».List.minIdxOn.go) f y j (j + 1) ys := rfl

theorem minOn_append_single {β α : Type _} [LE β] [DecidableLE β] {f : α → β} {xs : List α} (z : α)
    (hxs : xs ≠ []) : (xs ++ [z]).minOn f (by simp) = minOn f (xs.minOn f hxs) z := by
  match xs with
  | x :: xs => simp [List.minOn, List.foldl_append]

-- `List.minIdxOn_eq_go_drop`
theorem List.minIdxOn_eq_go_drop.h4 : drop% _private.Init.Data.List.MinMaxIdx.«0».List.minIdxOn_eq_go_drop 4 := by
  intro β α _ _ f xs h k
  match xs with
  | y :: ys =>
    simp only [List.drop_succ_cons]
    induction k
    · simp [List.minIdxOn, List.minOn]
    · rename_i k ih
      obtain ⟨i, hlt, hi, ih⟩ := ih
      simp only [ih, ← List.drop_drop]
      simp only [List.length_cons] at hlt
      match h : List.drop k ys with
      | [] =>
        have : ys.length ≤ k := by simp_all
        simp [List.drop_nil, minIdxGo_nil, List.take_of_length_le, hi, ih, hlt, this, Nat.le_succ_of_le]
      | z :: zs =>
        simp only [minIdxGo_cons]
        have : List.take (k + 1 + 1) (y :: ys) = List.take (k + 1) (y :: ys) ++ [z] :=
          (priv% _private.Init.Data.List.MinMaxIdx.«0».List.take_succ_eq_append_of_drop_eq_cons) ‹_›
        simp only [this, minOn_append_single z (xs := List.take (k + 1) (y :: ys)) (by simp)]
        simp only [List.take_succ_cons] at this
        split
        · simp only [minOn_eq_left, List.length_cons, *]
          exact ⟨i, by omega, Nat.le_succ_of_le ‹i ≤ k›, by simp [ih], rfl⟩
        · simp only [not_false_eq_true, minOn_eq_right, List.length_cons, *]
          obtain ⟨hlt, rfl⟩ := (priv% _private.Init.Data.List.MinMaxIdx.«0».List.exists_getElem_eq_of_drop_eq_cons) h
          exact ⟨k + 1, by omega, Nat.le_refl _, by simp, rfl⟩

/-- The writer monad `Nat × α` whose `bind` adds `1` to the counters (not lawful); `map` is the
default `bind`/`pure`. -/
def CB (α : Type) := Nat × α
instance : Monad CB where
  pure a := (0, a)
  bind x f := ((f x.2).1 + x.1 + 1, (f x.2).2)

-- `List.scanAuxM.go_eq_append_map`
theorem List.scanAuxM.go_eq_append_map.h7 : ¬ drop0% _private.Init.Data.List.Scan.Lemmas.«0».List.scanAuxM.go_eq_append_map 7 := fun h => by
  have := h (m := CB) (α := Nat) (β := Nat) (xs := []) (last := 0) (acc := []) (f := fun _ _ => ((0, 0) : Nat × Nat))
  have := congrArg (fun p : Nat × List Nat => p.1) this
  exact absurd this (by decide)

-- `List.scanAuxM_cons`
theorem List.scanAuxM_cons.h7 : ¬ drop0% _private.Init.Data.List.Scan.Lemmas.«0».List.scanAuxM_cons 7 := fun h => by
  have := h (m := CB) (α := Nat) (β := Nat) (init := 0) (x := 0) (xs := []) (f := fun _ _ => ((0, 0) : Nat × Nat))
  have := congrArg (fun p : Nat × List Nat => p.1) this
  exact absurd this (by decide)

-- `List.compareLex_append_append_of_not_prefix`
theorem List.compareLex_append_append_of_not_prefix.h2 : ¬ drop0% _private.Init.Data.Order.Ord.«0».List.compareLex_append_append_of_not_prefix 2 := fun h => by
  have := h (α := Bool) (cmp := fun _ _ => .eq) (l₁ := [true]) (l₂ := [false]) (l₃ := []) (l₄ := [true]) (by decide) (by decide)
  exact absurd this (by decide)

/-- `R1` on `Bool`: everything is related to `true` (so `true` is not accessible), nothing to `false`. -/
def R1 (_ b : Bool) : Prop := b = true

theorem acc_R1_false : Acc R1 false := ⟨_, fun _ h => nomatch h⟩

theorem not_acc_R1 : ∀ b, Acc R1 b → b ≠ true := by
  intro b h
  induction h with
  | intro x _ ih => intro hx; subst hx; exact ih true rfl rfl

theorem not_acc_R1_true : ¬ Acc R1 true := fun h => not_acc_R1 true h rfl

theorem not_wf_R1 : ¬ WellFounded R1 := fun h => not_acc_R1_true (h.apply true)

-- `WellFounded.fixGraph_fixC`
theorem WellFounded.fixGraph_fixC.h3 : ¬ indepu% [1, 0] _private.Init.WFComputable.«0».WellFounded.fixGraph_fixC 3 := fun h =>
  not_wf_R1 (h (α := Bool) (C := fun _ => True) (r := R1) (fun _ _ => trivial) false acc_R1_false)

-- `WellFounded.fixGraph_fixC`
theorem WellFounded.fixGraph_fixC.h6 : drop% _private.Init.WFComputable.«0».WellFounded.fixGraph_fixC 6 := by
  intro α C r hwf F x
  exact (priv% _private.Init.WFComputable.«0».WellFounded.fixGraph_fixC) hwf F x (hwf.apply x)

-- `WellFounded.fixGraph_fixFC`
theorem WellFounded.fixGraph_fixFC.h5 : ¬ indepu% [1, 0] _private.Init.WFComputable.«0».WellFounded.fixGraph_fixFC 5 := fun h =>
  not_acc_R1_true (h (α := Bool) (r := R1) (C := fun _ => True) (fun _ _ => trivial) true)

-- `repeatM.body_monotone_of_monadTail`
theorem repeatM.body_monotone_of_monadTail.h5 : ¬ indep0% _private.Init.Internal.Order.While.«0».repeatM.body_monotone_of_monadTail 5 := fun h =>
  (h (α := Unit) (m := Option) (β := Empty) (fun _ => none)).elim fun e => nomatch e

-- `instNonemptySubtypePred`
theorem instNonemptySubtypePred.h4 : ¬ drop0% _private.Init.While.«0».instNonemptySubtypePred 4 := fun h => by
  obtain ⟨⟨r, _⟩⟩ := h (α := Unit) (m := Id) (β := Empty) (f := fun _ => pure (.inl ())) (a := ())
  exact nomatch r

-- `repeatM_eq`
theorem repeatM_eq.h4 : ¬ indep0% _private.Init.While.«0».repeatM_eq 4 := fun h =>
  (h (α := Unit) (m := Option) (β := Empty) (f := fun _ => none) () ⟨fun _ => none, rfl⟩).elim fun e => nomatch e

/-- The lawful writer monad `Nat × α` (`bind` adds the counters). -/
def LWr (α : Type) := Nat × α
instance : Monad LWr where
  pure a := (0, a)
  bind x f := (x.1 + (f x.2).1, (f x.2).2)

-- `repeatM_eq`
theorem repeatM_eq.h7 : ¬ drop0% _private.Init.While.«0».repeatM_eq 7 := fun h => by
  have e := fun a => h (α := Unit) (m := LWr) (β := Nat) (f := fun _ => ((1, .inl ()) : Nat × (Unit ⊕ Nat))) a
  have := congrArg Prod.fst (e ())
  simp [repeatM.body, bind] at this

section Iterators
open Std Std.Iterators Std.Iterators.Types


theorem wf_irrefl {α : Sort u} {r : α → α → Prop} (h : WellFounded r) (a : α) : ¬ r a a := by
  have := h.apply a
  induction this with
  | intro x _ ih => exact fun hx => ih x hx hx

theorem not_finite_of_skip {α β : Type} {m : Type → Type} [Iterator α m β]
    (it : IterM (α := α) m β) (h : it.IsPlausibleStep (.skip it)) : ¬ Finite α m :=
  fun hf => wf_irrefl hf.wf it ⟨_, rfl, h⟩

theorem not_productive_of_skip {α β : Type} {m : Type → Type} [Iterator α m β]
    (it : IterM (α := α) m β) (h : it.IsPlausibleStep (.skip it)) : ¬ Productive α m :=
  fun hp => wf_irrefl hp.wf it h

/-- `LP β`: skips to itself (neither finite nor productive); from `OpABHand`. -/
structure LP (β : Type) where u : Unit

instance LP.inst {m : Type → Type} [Pure m] {β : Type} : Iterator (LP β) m β where
  IsPlausibleStep it s := s = .skip it
  step it := pure (.deflate ⟨.skip it, rfl⟩)

def LP.it {m : Type → Type} {β : Type} : IterM (α := LP β) m β := ⟨⟨()⟩⟩

theorem LP.skip {m : Type → Type} [Pure m] {β : Type} (it : IterM (α := LP β) m β) :
    it.IsPlausibleStep (.skip it) := rfl

theorem LP.not_finite {m : Type → Type} [Pure m] {β : Type} : ¬ Finite (LP β) m :=
  not_finite_of_skip LP.it (LP.skip _)

theorem LP.not_productive {m : Type → Type} [Pure m] {β : Type} : ¬ Productive (LP β) m :=
  not_productive_of_skip LP.it (LP.skip _)

/-- `S1 β`: state `true` skips to `false`, which is done (finite and productive). -/
structure S1 (β : Type) where b : Bool

def S1.stepv {m : Type → Type} {β : Type} : Bool → IterStep (IterM (α := S1 β) m β) β
  | true => .skip ⟨⟨false⟩⟩
  | false => .done

instance S1.inst {m : Type → Type} [Pure m] {β : Type} : Iterator (S1 β) m β where
  IsPlausibleStep it s := s = S1.stepv it.internalState.b
  step it := pure (.deflate ⟨S1.stepv it.internalState.b, rfl⟩)

def S1.t {m : Type → Type} {β : Type} : IterM (α := S1 β) m β := ⟨⟨true⟩⟩
def S1.f {m : Type → Type} {β : Type} : IterM (α := S1 β) m β := ⟨⟨false⟩⟩

theorem S1.skip {m : Type → Type} [Pure m] {β : Type} :
    (S1.t : IterM (α := S1 β) m β).IsPlausibleStep (.skip S1.f) := rfl

theorem S1.acc_false {m : Type → Type} [Pure m] {β : Type} :
    Acc IterM.IsPlausibleSuccessorOf (S1.f : IterM (α := S1 β) m β) :=
  ⟨_, fun b ⟨s, hs, hp⟩ => by subst hp; cases hs⟩

instance S1.finite {m : Type → Type} [Pure m] {β : Type} : Finite (S1 β) m :=
  ⟨⟨fun ⟨⟨b⟩⟩ => match b with
    | false => S1.acc_false
    | true => ⟨_, fun b' ⟨s, hs, hp⟩ => by
        subst hp; simp only [S1.stepv, IterStep.successor, Option.some.injEq] at hs; subst hs
        exact S1.acc_false⟩⟩⟩

abbrev IA := IterM (α := S1 Nat) Id Nat
abbrev IL := IterM (α := LP Nat) Id Nat

-- `Std.Iterators.Types.Flatten.rel_of_left`
theorem Flatten.rel_of_left.h7 : ¬ indep0% _private.Init.Data.Iterators.Combinators.Monadic.FlatMap.«0».Std.Iterators.Types.Flatten.rel_of_left 7 := fun h =>
  LP.not_finite (h (α := LP IA) (α₂ := S1 Nat) (β := Nat) (m := Id) (it := ⟨⟨LP.it, none⟩⟩) (it' := ⟨⟨LP.it, none⟩⟩))

-- `Std.Iterators.Types.Flatten.rel_of_left`
theorem Flatten.rel_of_left.h8 : ¬ indep0% _private.Init.Data.Iterators.Combinators.Monadic.FlatMap.«0».Std.Iterators.Types.Flatten.rel_of_left 8 := fun h =>
  LP.not_finite (@h (S1 IL) (LP Nat) Nat Id _ _ _ S1.finite (⟨⟨S1.t, none⟩⟩) (⟨⟨S1.f, none⟩⟩)
    (IterM.TerminationMeasures.Finite.rel_of_skip S1.skip))

-- `Std.Iterators.Types.Flatten.rel_of_left`
theorem Flatten.rel_of_left.h11 : ¬ drop0% _private.Init.Data.Iterators.Combinators.Monadic.FlatMap.«0».Std.Iterators.Types.Flatten.rel_of_left 11 := fun h => by
  have := h (α := S1 IA) (α₂ := S1 Nat) (β := Nat) (m := Id) (it := ⟨⟨S1.f, none⟩⟩) (it' := ⟨⟨S1.f, none⟩⟩)
  have hwf := ((priv% _private.Init.Data.Iterators.Combinators.Monadic.FlatMap.«0».Std.Iterators.Types.Flatten.instFinitenessRelation) (α := S1 IA) (α₂ := S1 Nat) (β := Nat) (m := Id)).wf
  exact wf_irrefl hwf _ this

-- `Std.Iterators.Types.Flatten.rel_of_right₁`
theorem Flatten.rel_of_right₁.h7 : ¬ indep0% _private.Init.Data.Iterators.Combinators.Monadic.FlatMap.«0».Std.Iterators.Types.Flatten.rel_of_right₁ 7 := fun h =>
  LP.not_finite (h (α := LP IA) (α₂ := S1 Nat) (β := Nat) (m := Id) (it₁ := LP.it) (it₂ := S1.t) (it₂' := S1.f)
    (IterM.TerminationMeasures.Finite.rel_of_skip S1.skip))

-- `Std.Iterators.Types.Flatten.rel_of_right₁`
theorem Flatten.rel_of_right₁.h8 : ¬ indep0% _private.Init.Data.Iterators.Combinators.Monadic.FlatMap.«0».Std.Iterators.Types.Flatten.rel_of_right₁ 8 := fun h =>
  LP.not_finite (@h (S1 IL) (LP Nat) Nat Id _ _ _ S1.finite (S1.t) (LP.it) (LP.it))

-- `Std.Iterators.Types.Flatten.rel_of_right₁`
theorem Flatten.rel_of_right₁.h12 : ¬ drop0% _private.Init.Data.Iterators.Combinators.Monadic.FlatMap.«0».Std.Iterators.Types.Flatten.rel_of_right₁ 12 := fun h => by
  have := h (α := S1 IA) (α₂ := S1 Nat) (β := Nat) (m := Id) (it₁ := S1.f) (it₂ := S1.f) (it₂' := S1.f)
  have hwf := ((priv% _private.Init.Data.Iterators.Combinators.Monadic.FlatMap.«0».Std.Iterators.Types.Flatten.instFinitenessRelation) (α := S1 IA) (α₂ := S1 Nat) (β := Nat) (m := Id)).wf
  exact wf_irrefl hwf _ this

-- `Std.Iterators.Types.Flatten.rel_of_right₂`
theorem Flatten.rel_of_right₂.h7 : ¬ indep0% _private.Init.Data.Iterators.Combinators.Monadic.FlatMap.«0».Std.Iterators.Types.Flatten.rel_of_right₂ 7 := fun h =>
  LP.not_finite (h (α := LP IA) (α₂ := S1 Nat) (β := Nat) (m := Id) (it₁ := LP.it) (it₂ := S1.t))

-- `Std.Iterators.Types.Flatten.rel_of_right₂`
theorem Flatten.rel_of_right₂.h8 : ¬ indep0% _private.Init.Data.Iterators.Combinators.Monadic.FlatMap.«0».Std.Iterators.Types.Flatten.rel_of_right₂ 8 := fun h =>
  LP.not_finite (@h (S1 IL) (LP Nat) Nat Id _ _ _ S1.finite (S1.t) (LP.it))

-- `Std.Iterators.Types.Flatten.productiveRel_of_left`
theorem Flatten.productiveRel_of_left.h7 : ¬ indep0% _private.Init.Data.Iterators.Combinators.Monadic.FlatMap.«0».Std.Iterators.Types.Flatten.productiveRel_of_left 7 := fun h =>
  LP.not_finite (h (α := LP IA) (α₂ := S1 Nat) (β := Nat) (m := Id) (it := ⟨⟨LP.it, none⟩⟩) (it' := ⟨⟨LP.it, none⟩⟩))

-- `Std.Iterators.Types.Flatten.productiveRel_of_left`
theorem Flatten.productiveRel_of_left.h8 : ¬ indep0% _private.Init.Data.Iterators.Combinators.Monadic.FlatMap.«0».Std.Iterators.Types.Flatten.productiveRel_of_left 8 := fun h =>
  LP.not_productive (@h (S1 IL) (LP Nat) Nat Id _ _ _ S1.finite (⟨⟨S1.t, none⟩⟩) (⟨⟨S1.f, none⟩⟩)
    (IterM.TerminationMeasures.Finite.rel_of_skip S1.skip))

-- `Std.Iterators.Types.Flatten.productiveRel_of_left`
theorem Flatten.productiveRel_of_left.h11 : ¬ drop0% _private.Init.Data.Iterators.Combinators.Monadic.FlatMap.«0».Std.Iterators.Types.Flatten.productiveRel_of_left 11 := fun h => by
  have := h (α := S1 IA) (α₂ := S1 Nat) (β := Nat) (m := Id) (it := ⟨⟨S1.f, none⟩⟩) (it' := ⟨⟨S1.f, none⟩⟩)
  have hwf := ((priv% _private.Init.Data.Iterators.Combinators.Monadic.FlatMap.«0».Std.Iterators.Types.Flatten.instProductivenessRelation) (α := S1 IA) (α₂ := S1 Nat) (β := Nat) (m := Id)).wf
  exact wf_irrefl hwf _ this

-- `Std.Iterators.Types.Flatten.productiveRel_of_right₁`
theorem Flatten.productiveRel_of_right₁.h7 : ¬ indep0% _private.Init.Data.Iterators.Combinators.Monadic.FlatMap.«0».Std.Iterators.Types.Flatten.productiveRel_of_right₁ 7 := fun h =>
  LP.not_finite (h (α := LP IA) (α₂ := S1 Nat) (β := Nat) (m := Id) (it₁ := LP.it) (it₂ := S1.t) (it₂' := S1.f)
    (IterM.TerminationMeasures.Productive.rel_of_skip S1.skip))

-- `Std.Iterators.Types.Flatten.productiveRel_of_right₁`
theorem Flatten.productiveRel_of_right₁.h8 : ¬ indep0% _private.Init.Data.Iterators.Combinators.Monadic.FlatMap.«0».Std.Iterators.Types.Flatten.productiveRel_of_right₁ 8 := fun h =>
  LP.not_productive (@h (S1 IL) (LP Nat) Nat Id _ _ _ S1.finite (S1.t) (LP.it) (LP.it))

-- `Std.Iterators.Types.Flatten.productiveRel_of_right₁`
theorem Flatten.productiveRel_of_right₁.h12 : ¬ drop0% _private.Init.Data.Iterators.Combinators.Monadic.FlatMap.«0».Std.Iterators.Types.Flatten.productiveRel_of_right₁ 12 := fun h => by
  have := h (α := S1 IA) (α₂ := S1 Nat) (β := Nat) (m := Id) (it₁ := S1.f) (it₂ := S1.f) (it₂' := S1.f)
  have hwf := ((priv% _private.Init.Data.Iterators.Combinators.Monadic.FlatMap.«0».Std.Iterators.Types.Flatten.instProductivenessRelation) (α := S1 IA) (α₂ := S1 Nat) (β := Nat) (m := Id)).wf
  exact wf_irrefl hwf _ this

-- `Std.Iterators.Types.Flatten.productiveRel_of_right₂`
theorem Flatten.productiveRel_of_right₂.h7 : ¬ indep0% _private.Init.Data.Iterators.Combinators.Monadic.FlatMap.«0».Std.Iterators.Types.Flatten.productiveRel_of_right₂ 7 := fun h =>
  LP.not_finite (h (α := LP IA) (α₂ := S1 Nat) (β := Nat) (m := Id) (it₁ := LP.it) (it₂ := S1.t))

-- `Std.Iterators.Types.Flatten.productiveRel_of_right₂`
theorem Flatten.productiveRel_of_right₂.h8 : ¬ indep0% _private.Init.Data.Iterators.Combinators.Monadic.FlatMap.«0».Std.Iterators.Types.Flatten.productiveRel_of_right₂ 8 := fun h =>
  LP.not_productive (@h (S1 IL) (LP Nat) Nat Id _ _ _ S1.finite (S1.t) (LP.it))


/-- `map` adds 1 (`id_map` fails); `bind` adds the counts (from `ItMonadMBHand`). -/
structure MW (α : Type) where
  c : Int
  v : α
instance : Monad MW where
  pure a := ⟨0, a⟩
  bind {α β} x f := ⟨x.c + (f x.v).c, (f x.v).v⟩
  map {α β} f x := ⟨x.c + 1, f x.v⟩
@[simp] theorem MW.pure_def (a : α) : (pure a : MW α) = ⟨0, a⟩ := id rfl
@[simp] theorem MW.bind_def (x : MW α) (f : α → MW β) : x >>= f = ⟨x.c + (f x.v).c, (f x.v).v⟩ := id rfl
@[simp] theorem MW.map_def (x : MW α) (f : α → β) : f <$> x = ⟨x.c + 1, f x.v⟩ := id rfl

/-- Lawful writer with `Nat` counts (`bind` adds). -/
structure LN (α : Type) where
  c : Nat
  v : α
instance : Monad LN where
  pure a := ⟨0, a⟩
  bind {α β} x f := ⟨x.c + (f x.v).c, (f x.v).v⟩
  map {α β} f x := ⟨x.c, f x.v⟩
@[simp] theorem LN.pure_def (a : α) : (pure a : LN α) = ⟨0, a⟩ := id rfl
@[simp] theorem LN.bind_def (x : LN α) (f : α → LN β) : x >>= f = ⟨x.c + (f x.v).c, (f x.v).v⟩ := id rfl
@[simp] theorem LN.map_def (x : LN α) (f : α → β) : f <$> x = ⟨x.c, f x.v⟩ := id rfl
instance : LawfulMonad LN := LawfulMonad.mk' _ (fun _ => rfl)
  (fun _ _ => by simp [bind, pure]) (fun _ _ _ => by simp [bind, Nat.add_assoc])
  (bind_pure_comp := fun _ _ => by simp [bind, pure, Functor.map])

/-- `YC`: yields `0` and stays, and each step counts `1` in `LN` (productive, not finite). -/
structure YC where u : Unit
instance : Iterator YC LN Nat where
  IsPlausibleStep it s := s = .yield it 0
  step it := ⟨1, .deflate ⟨.yield it 0, rfl⟩⟩
def YC.it : IterM (α := YC) LN Nat := ⟨⟨()⟩⟩

theorem no_descent {γ : Type} (c : γ → Nat) (s : γ → γ) (h : ∀ a, c a = 1 + c (s a)) (a : γ) : False := by
  have key : ∀ k a, k ≤ c a := by
    intro k
    induction k with
    | zero => intro; exact Nat.zero_le _
    | succ k ih => intro a; rw [h]; have := ih (s a); omega
  have := key (c a + 1) a
  omega

theorem go_eq' {α β : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β] [Finite α m]
    {it : IterM (α := α) m β} {acc : Array β} :
    IterM.toArray.go it acc = (do
      match (← it.step).inflate with
      | .yield it' out h => IterM.toArray.go it' (acc.push out)
      | .skip it' h => IterM.toArray.go it' acc
      | .done _ => return acc) := by
  rw [IterM.toArray.go, WellFounded.extrinsicFix₂_eq_apply]
  · rfl
  · exact InvImage.wf _ WellFoundedRelation.wf

theorem revgo_eq' {α β : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β] [Finite α m]
    {it : IterM (α := α) m β} {acc : List β} :
    IterM.toListRev.go it acc = (do
      match (← it.step).inflate with
      | .yield it' out h => IterM.toListRev.go it' (out :: acc)
      | .skip it' h => IterM.toListRev.go it' acc
      | .done _ => return acc) := by
  rw [IterM.toListRev.go, WellFounded.extrinsicFix₂_eq_apply]
  · apply bind_congr; intro step
    generalize step.inflate = s
    rcases s with ⟨_ | _ | _, _⟩ <;> rfl
  · exact InvImage.wf _ WellFoundedRelation.wf

theorem step_iterM_nil {α : Type w} {m : Type w → Type w'} [Pure m] :
    ([].iterM m : IterM (α := ListIterator α) m α).step = pure (.deflate ⟨.done, rfl⟩) := rfl

theorem step_iterM_cons {α : Type w} {m : Type w → Type w'} [Pure m] {x : α} {xs : List α} :
    ((x :: xs).iterM m).step = pure (.deflate ⟨.yield (xs.iterM m) x, rfl⟩) := rfl

abbrev en : IterM (α := ListIterator Nat) MW Nat := ([] : List Nat).iterM MW

-- `Std.IterM.toArray.go.aux₁`
theorem IterM.toArray.go.aux₁.h5 : ¬ drop0% _private.Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect.«0».Std.IterM.toArray.go.aux₁ 5 := fun h => by
  have := congrArg MW.c (h (m := MW) (it := en) (b := 0) (bs := #[]))
  rw [go_eq', go_eq'] at this
  simp [Shrink.inflate_deflate] at this

-- `Std.IterM.toArray.go.aux₂`
theorem IterM.toArray.go.aux₂.h5 : ¬ drop0% _private.Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect.«0».Std.IterM.toArray.go.aux₂ 5 := fun h => by
  have := congrArg MW.c (h (m := MW) (it := en) (acc := #[]))
  rw [IterM.toArray, go_eq'] at this
  simp [Shrink.inflate_deflate] at this

-- `Std.IterM.toListRev.go.aux₁`
theorem IterM.toListRev.go.aux₁.h4 : ¬ drop0% _private.Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect.«0».Std.IterM.toListRev.go.aux₁ 4 := fun h => by
  have := congrArg MW.c (h (m := MW) (it := en) (b := 0) (bs := []))
  rw [revgo_eq', revgo_eq'] at this
  simp [Shrink.inflate_deflate] at this

-- `Std.IterM.toListRev.go.aux₂`
theorem IterM.toListRev.go.aux₂.h4 : ¬ drop0% _private.Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect.«0».Std.IterM.toListRev.go.aux₂ 4 := fun h => by
  have := congrArg MW.c (h (m := MW) (it := en) (acc := []))
  rw [IterM.toListRev, revgo_eq'] at this
  simp [Shrink.inflate_deflate] at this

-- `Std.IterM.toArray.go_eq`
theorem IterM.toArray.go_eq.h7 : ¬ drop0% _private.Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect.«0».Std.IterM.toArray.go_eq 7 := fun h => by
  refine no_descent (fun acc => (IterM.toArray.go YC.it acc).c) (fun acc => acc.push 0) (fun acc => ?_) #[]
  have := congrArg LN.c (h (m := LN) (it := YC.it) (acc := acc))
  simpa [Shrink.inflate_deflate, IterM.step, Iterator.step] using this

-- `Std.IterM.toListRev.go_eq`
theorem IterM.toListRev.go_eq.h6 : ¬ drop0% _private.Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect.«0».Std.IterM.toListRev.go_eq 6 := fun h => by
  refine no_descent (fun bs => (IterM.toListRev.go YC.it bs).c) (fun bs => 0 :: bs) (fun bs => ?_) []
  have := congrArg LN.c (h (m := LN) (it := YC.it) (bs := bs))
  simpa [Shrink.inflate_deflate, IterM.step, Iterator.step] using this


/-- `bind` counts itself (`pure_bind` fails); `map`, `attach` keep the count (from `ItMonadMBHand`). -/
structure BW (α : Type) where
  c : Int
  v : α
instance : Monad BW where
  pure a := ⟨0, a⟩
  bind {α β} x f := ⟨x.c + (f x.v).c + 1, (f x.v).v⟩
  map {α β} f x := ⟨x.c, f x.v⟩
instance : MonadAttach BW where
  CanReturn x a := a = x.v
  attach {α} x := ⟨x.c, ⟨x.v, rfl⟩⟩
@[simp] theorem BW.pure_def (a : α) : (pure a : BW α) = ⟨0, a⟩ := id rfl
@[simp] theorem BW.bind_def (x : BW α) (f : α → BW β) : x >>= f = ⟨x.c + (f x.v).c + 1, (f x.v).v⟩ := id rfl
@[simp] theorem BW.map_def (x : BW α) (f : α → β) : f <$> x = ⟨x.c, f x.v⟩ := id rfl
@[simp] theorem BW.attachLift_op (x : BW α) :
    (PostconditionT.attachLift x).operation = ⟨x.c, ⟨x.v, rfl⟩⟩ := id rfl
instance : WeaklyLawfulMonadAttach BW := ⟨by intro _ x; simp [Functor.map, MonadAttach.attach]⟩

/-- Lawful writer whose `attach` adds 1 (`map_attach` fails; from `ItMonadMBHand`). -/
structure AW (α : Type) where
  c : Int
  v : α
instance : Monad AW where
  pure a := ⟨0, a⟩
  bind {α β} x f := ⟨x.c + (f x.v).c, (f x.v).v⟩
  map {α β} f x := ⟨x.c, f x.v⟩
instance : MonadAttach AW where
  CanReturn x a := a = x.v
  attach {α} x := ⟨x.c + 1, ⟨x.v, rfl⟩⟩
@[simp] theorem AW.pure_def (a : α) : (pure a : AW α) = ⟨0, a⟩ := id rfl
@[simp] theorem AW.bind_def (x : AW α) (f : α → AW β) : x >>= f = ⟨x.c + (f x.v).c, (f x.v).v⟩ := id rfl
@[simp] theorem AW.map_def (x : AW α) (f : α → β) : f <$> x = ⟨x.c, f x.v⟩ := id rfl
@[simp] theorem AW.attachLift_op (x : AW α) :
    (PostconditionT.attachLift x).operation = ⟨x.c + 1, ⟨x.v, rfl⟩⟩ := id rfl
instance : LawfulMonad AW := LawfulMonad.mk' _ (fun _ => rfl)
  (fun _ _ => by simp [bind, pure]) (fun _ _ _ => by simp [bind, Int.add_assoc])
  (bind_pure_comp := fun _ _ => by simp [bind, pure, Functor.map])

/-- The private `Std.IterM.flattenAfter`. -/
elab "FA%" : term =>
  mkConstWithFreshMVarLevels (hcFixName `_private.Init.Data.Iterators.Combinators.Monadic.FlatMap.«0».Std.IterM.flattenAfter)

theorem step_flattenAfter' {α α₂ β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m (IterM (α := α₂) m β)] [Iterator α₂ m β]
    {it₁ : IterM (α := α) m (IterM (α := α₂) m β)} {it₂ : Option (IterM (α := α₂) m β)} :
  ((FA%) it₁ it₂).step = (
    match it₂ with
    | none => do
      match (← it₁.step).inflate with
      | .yield it₁' it₂' h => return .deflate (.skip ((FA%) it₁' (some it₂')) (.outerYield h))
      | .skip it₁' h => return .deflate (.skip ((FA%) it₁' none) (.outerSkip h))
      | .done h => return .deflate (.done (.outerDone h))
    | some it₂ => do
      match (← it₂.step).inflate with
      | .yield it₂' out h => return .deflate (.yield ((FA%) it₁ (some it₂')) out (.innerYield h))
      | .skip it₂' h => return .deflate (.skip ((FA%) it₁ (some it₂')) (.innerSkip h))
      | .done h => return .deflate (.skip ((FA%) it₁ none) (.innerDone h))) := by
  cases it₂
  all_goals
  · apply bind_congr; intro step
    cases step.inflate using PlausibleIterStep.casesOn <;> rfl

theorem step_mwp {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] {it : IterM (α := α) m β} {f : β → PostconditionT n γ}
    [Monad n] [MonadLiftT m n] :
  (it.mapWithPostcondition f).step = (do
    match (← it.step).inflate with
    | .yield it' out h => do
      match ← (PostconditionT.map some (f out)).operation with
      | ⟨none, h'⟩ =>
        pure <| .deflate <| .skip (it'.mapWithPostcondition f) (.yieldNone (out := out) h h')
      | ⟨some out', h'⟩ =>
        pure <| .deflate <| .yield (it'.mapWithPostcondition f) out' (.yieldSome (out := out) h h')
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.mapWithPostcondition f) (.skip h)
    | .done h =>
      pure <| .deflate <| .done (by exact .done h)) := by
  apply bind_congr
  intro step
  match step.inflate with
  | .yield it' out h =>
    simp only [PlausibleIterStep.skip, PlausibleIterStep.yield]
    apply bind_congr
    intro step
    rcases step with _ | _ <;> rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem step_fmwp {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] {it : IterM (α := α) m β} {f : β → PostconditionT n (Option γ)}
    [Monad n] [MonadLiftT m n] :
  (it.filterMapWithPostcondition f).step = (do
    match (← it.step).inflate with
    | .yield it' out h => do
      match ← (f out).operation with
      | ⟨none, h'⟩ =>
        pure <| .deflate <| .skip (it'.filterMapWithPostcondition f) (.yieldNone (out := out) h h')
      | ⟨some out', h'⟩ =>
        pure <| .deflate <| .yield (it'.filterMapWithPostcondition f) out' (.yieldSome (out := out) h h')
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.filterMapWithPostcondition f) (.skip h)
    | .done h =>
      pure <| .deflate <| .done (by exact .done h)) := by
  apply bind_congr
  intro step
  match step.inflate with
  | .yield it' out h =>
    simp only [PlausibleIterStep.skip, PlausibleIterStep.yield]
    apply bind_congr
    intro step
    rcases step with _ | _ <;> rfl
  | .skip it' h => rfl
  | .done h => rfl

@[congr] theorem fmwp_congr {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [MonadLiftT m n] [Iterator α m β] {f : β → PostconditionT n (Option γ)} {it it' : IterM (α := α) m β}
    (h : it = it') : it.filterMapWithPostcondition f = it'.filterMapWithPostcondition f := h ▸ rfl

theorem pc_pure_op {m : Type w → Type w'} [Monad m] (a : α) :
    (pure a : PostconditionT m α).operation = pure ⟨a, rfl⟩ := rfl

theorem mapM_eq {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [Iterator α m β]
    [Monad n] [MonadAttach n] [MonadLiftT m n] {f : β → n γ} {it : IterM (α := α) m β} :
    it.mapM f = it.mapWithPostcondition (fun b => PostconditionT.attachLift (f b)) := id rfl

@[congr] theorem mwp_congr {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [Monad n]
    [MonadLiftT m n] [Iterator α m β] {f : β → PostconditionT n γ} {it it' : IterM (α := α) m β}
    (h : it = it') : it.mapWithPostcondition f = it'.mapWithPostcondition f := h ▸ rfl

syntax "ev" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| ev $[$loc]?) => `(tactic| simp only [BW.pure_def, BW.bind_def, BW.map_def, BW.attachLift_op,
      AW.pure_def, AW.bind_def, AW.map_def, AW.attachLift_op, step_iterM_nil, step_iterM_cons, step_flattenAfter',
      step_mwp, step_fmwp, pc_pure_op, Id.run_pure, Id.run_bind, Id.run_map, mapM_eq, monadLift_self, PostconditionT.operation_map, Shrink.inflate_deflate, Array.push,
      List.concat, List.nil_append, List.cons_append, pure_bind, ↓reduceIte] $[$loc]?)

macro "evh" h:ident : tactic => `(tactic| (
  repeat ((first | rw [go_eq'] at $h:ident | rw [IterM.toList] at $h:ident | rw [IterM.toArray] at $h:ident); try ev at $h:ident)))

abbrev LB := IterM (α := ListIterator Nat) BW Nat
abbrev LA := IterM (α := ListIterator Nat) AW Nat

-- `Std.IterM.toList_flattenAfter`
theorem IterM.toList_flattenAfter.h6 : ¬ drop0% _private.Init.Data.Iterators.Lemmas.Combinators.Monadic.FlatMap.«0».Std.IterM.toList_flattenAfter 6 := fun h => by
  have := h (m := BW) (it₁ := ([] : List LB).iterM BW) (it₂ := some (([] : List Nat).iterM BW))
  have := congrArg BW.c this
  evh this
  simp at this

-- `Std.IterM.toArray_flattenAfter`
theorem IterM.toArray_flattenAfter.h6 : ¬ drop0% _private.Init.Data.Iterators.Lemmas.Combinators.Monadic.FlatMap.«0».Std.IterM.toArray_flattenAfter 6 := fun h => by
  have := h (m := BW) (it₁ := ([] : List LB).iterM BW) (it₂ := some (([] : List Nat).iterM BW))
  have := congrArg BW.c this
  evh this
  simp at this

-- `Std.IterM.toList_flattenAfter`
theorem IterM.toList_flattenAfter.h7 : ¬ drop0% _private.Init.Data.Iterators.Lemmas.Combinators.Monadic.FlatMap.«0».Std.IterM.toList_flattenAfter 7 := fun h => by
  have := h (m := AW) (it₁ := [([] : List Nat).iterM AW].iterM AW) (it₂ := none)
  have := congrArg AW.c this
  evh this
  simp at this

-- `Std.IterM.toArray_flattenAfter`
theorem IterM.toArray_flattenAfter.h7 : ¬ drop0% _private.Init.Data.Iterators.Lemmas.Combinators.Monadic.FlatMap.«0».Std.IterM.toArray_flattenAfter 7 := fun h => by
  have := h (m := AW) (it₁ := [([] : List Nat).iterM AW].iterM AW) (it₂ := none)
  have := congrArg AW.c this
  evh this
  simp at this

-- `Std.IterM.toList_filterMapWithPostcondition_filterMapWithPostcondition'`
theorem IterM.toList_fMWP_fMWP'.h23 : ¬ drop0% _private.Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap.«0».Std.IterM.toList_filterMapWithPostcondition_filterMapWithPostcondition' 23 := fun h => by
  have := h (m := Id) (n := Id) (o := Id) (it := [0].iterM Id) (f := fun b => pure (some b)) (g := fun c => pure (some c))
    (fg := fun _ => pure none)
  evh this
  simp at this

/-! ### Support for the independent (opaque-fixpoint) rows

Each lemma derives `¬T'` from an assignment of values to the opaque collector terms (`opaqueFix₂`
at a non-`Finite` iterator type), which nothing in the kernel fixes. -/

abbrev LI := IterM (α := LP Nat) Id Nat

-- support: toArray.go.aux₁ (Finite) on LP over Id, go LP (#[0] ++ #[]) = #[] and go LP #[] = #[]
theorem IterM.toArray.go.aux₁.h7_neg (h₁ : IterM.toArray.go (LP.it : LI) (#[0] ++ #[]) = (#[] : Array Nat))
    (h₂ : IterM.toArray.go (LP.it : LI) #[] = (#[] : Array Nat)) :
    ¬ drop0% _private.Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect.«0».Std.IterM.toArray.go.aux₁ 7 := fun h => by
  have := h (m := Id) (it := (LP.it : LI)) (b := 0) (bs := #[])
  rw [h₁, h₂] at this
  exact absurd (congrArg (fun a : Array Nat => a.size) this) (by decide)

-- support: toArray.go.aux₂ (Finite) on LP over Id, go LP #[0] = #[] and LP.toArray = #[]
theorem IterM.toArray.go.aux₂.h7_neg (h₁ : IterM.toArray.go (LP.it : LI) #[0] = (#[] : Array Nat))
    (h₂ : (LP.it : LI).toArray = (#[] : Array Nat)) :
    ¬ drop0% _private.Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect.«0».Std.IterM.toArray.go.aux₂ 7 := fun h => by
  have := h (m := Id) (it := (LP.it : LI)) (acc := #[0])
  rw [h₁, h₂] at this
  exact absurd (congrArg (fun a : Array Nat => a.size) this) (by decide)

-- support: toListRev.go.aux₁ (Finite) on LP over Id, go LP ([] ++ [0]) = [] and go LP [] = []
theorem IterM.toListRev.go.aux₁.h6_neg (h₁ : IterM.toListRev.go (LP.it : LI) ([] ++ [0]) = ([] : List Nat))
    (h₂ : IterM.toListRev.go (LP.it : LI) [] = ([] : List Nat)) :
    ¬ drop0% _private.Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect.«0».Std.IterM.toListRev.go.aux₁ 6 := fun h => by
  have := h (m := Id) (it := (LP.it : LI)) (b := 0) (bs := [])
  rw [h₁, h₂] at this
  exact absurd (congrArg (fun a : List Nat => a.length) this) (by decide)

-- support: toListRev.go.aux₂ (Finite) on LP over Id, go LP [0] = [] and LP.toListRev = []
theorem IterM.toListRev.go.aux₂.h6_neg (h₁ : IterM.toListRev.go (LP.it : LI) [0] = ([] : List Nat))
    (h₂ : (LP.it : LI).toListRev = ([] : List Nat)) :
    ¬ drop0% _private.Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect.«0».Std.IterM.toListRev.go.aux₂ 6 := fun h => by
  have := h (m := Id) (it := (LP.it : LI)) (acc := [0])
  rw [h₁, h₂] at this
  exact absurd (congrArg (fun a : List Nat => a.length) this) (by decide)

abbrev LLI := IterM (α := LP (IterM (α := ListIterator Nat) Id Nat)) Id (IterM (α := ListIterator Nat) Id Nat)
abbrev ELI := IterM (α := ListIterator LI) Id LI

-- support: toList_flattenAfter (Finite α) with the outer iterator LP over Id, it₂ = none
theorem IterM.toList_flattenAfter.h10_neg (h₁ : ((FA%) (LP.it : LLI) none).toList = ([0] : List Nat))
    (h₂ : (IterM.mapM (fun it₂ => it₂.toList) (LP.it : LLI)).toList = ([] : List (List Nat))) :
    ¬ drop0% _private.Init.Data.Iterators.Lemmas.Combinators.Monadic.FlatMap.«0».Std.IterM.toList_flattenAfter 10 := fun h => by
  have := h (m := Id) (it₁ := (LP.it : LLI)) (it₂ := none)
  rw [h₁] at this
  simp only [h₂] at this
  exact absurd (congrArg (fun a : List Nat => a.length) this) (by decide)

-- support: toArray_flattenAfter (Finite α) with the outer iterator LP over Id, it₂ = none
theorem IterM.toArray_flattenAfter.h10_neg (h₁ : ((FA%) (LP.it : LLI) none).toArray = (#[0] : Array Nat))
    (h₂ : (IterM.mapM (fun it₂ => it₂.toArray) (LP.it : LLI)).toArray = (#[] : Array (Array Nat))) :
    ¬ drop0% _private.Init.Data.Iterators.Lemmas.Combinators.Monadic.FlatMap.«0».Std.IterM.toArray_flattenAfter 10 := fun h => by
  have := h (m := Id) (it₁ := (LP.it : LLI)) (it₂ := none)
  rw [h₁] at this
  simp only [h₂] at this
  exact absurd (congrArg (fun a : Array Nat => a.size) this) (by decide)

-- support: toList_flattenAfter (Finite α₂) with inner iterators LP over Id, outer list empty, it₂ = none
theorem IterM.toList_flattenAfter.h11_neg (h₁ : ((FA%) (([] : List LI).iterM Id : ELI) none).toList = ([0] : List Nat)) :
    ¬ drop0% _private.Init.Data.Iterators.Lemmas.Combinators.Monadic.FlatMap.«0».Std.IterM.toList_flattenAfter 11 := fun h => by
  have := h (m := Id) (it₁ := (([] : List LI).iterM Id : ELI)) (it₂ := none)
  rw [h₁] at this
  evh this
  exact absurd (congrArg (fun a : List Nat => a.length) this) (by decide)

-- support: toArray_flattenAfter (Finite α₂) with inner iterators LP over Id, outer list empty, it₂ = none
theorem IterM.toArray_flattenAfter.h11_neg (h₁ : ((FA%) (([] : List LI).iterM Id : ELI) none).toArray = (#[0] : Array Nat)) :
    ¬ drop0% _private.Init.Data.Iterators.Lemmas.Combinators.Monadic.FlatMap.«0».Std.IterM.toArray_flattenAfter 11 := fun h => by
  have := h (m := Id) (it₁ := (([] : List LI).iterM Id : ELI)) (it₂ := none)
  rw [h₁] at this
  evh this
  exact absurd (congrArg (fun a : Array Nat => a.size) this) (by decide)

-- support: filterMapWithPostcondition twice vs fused (Finite α) on LP over Id, f = g = fg = pure ∘ some
theorem IterM.toList_fMWP_fMWP'.h18_neg
    (h₁ : ((LP.it : LI).filterMapWithPostcondition (fun b => (pure (some b) : PostconditionT Id (Option Nat)))
      |>.filterMapWithPostcondition (fun b => (pure (some b) : PostconditionT Id (Option Nat)))).toList = ([] : List Nat))
    (h₂ : ((LP.it : LI).filterMapWithPostcondition (fun b => (pure (some b) : PostconditionT Id (Option Nat)))).toList = ([0] : List Nat)) :
    ¬ drop0% _private.Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap.«0».Std.IterM.toList_filterMapWithPostcondition_filterMapWithPostcondition' 18 := fun h => by
  have := h (m := Id) (n := Id) (o := Id) (it := (LP.it : LI)) (f := fun b => pure (some b)) (g := fun b => pure (some b))
    (fg := fun b => pure (some b)) (fun _ => rfl)
  rw [h₁, h₂] at this
  exact absurd (congrArg (fun a : List Nat => a.length) this) (by decide)

end Iterators

end DataMiscHand
