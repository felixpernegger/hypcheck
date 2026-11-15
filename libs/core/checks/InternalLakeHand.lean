import Std
import Lake
import Lake.Load.Resolve

/-!
Hand pass `InternalLake` (hand16): the 19 hypotheses of the 6 theorems with internal-style names
and in the Lake modules that the `Lake` root doesn't import (`results/internal_names_and_lake_unimported.jsonl`).
19 necessary.

* 16 hypotheses of the generated congruence lemmas `….match_1.congr` of four `Ordering` matchers in
  `Std.Data.DTreeMap.Internal.Model`. Their motive `α : Sort u` must be a type: for `u = 0` both
  sides are proofs of one proposition and the weakened statements hold, so these refutations use
  `drop1%`/`indep1%` (universe `1`, `α := Nat`). `ho : o = o'`: `o := .lt`, `o' := .gt`. Each branch
  premise: `o = o' :=` that branch, the two branch functions `0` and `1`.
* 3 hypotheses of the private theorems `Workspace.size_packages_setDepIdxs` and `ResolveState.lt_of_mem`
  in `Lake.Load.Resolve`. Their names have a numeric component, so they are stated with `dropS%`/`indepS%`
  (which read the statement off the private name) and are not covered by `check_hand.py`. Models: the
  one-package workspace `ws1` (copied from `checks/LeanLakeHand.lean`), a package with index 5 resp. the
  dependency index 1, and `ResolveState.init ws1 0` with `i := ws.packages.size`.
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
/-- `drop1% T i`: `drop% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "drop1% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.one
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

open Lean Meta Elab Term in
/-- `indep1% T i`: `indep% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "indep1% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.one
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



/-- The name written as a string, with numeric components (for private names such as `_private.M.0.x`). -/
def parseName (s : String) : Lean.Name :=
  (s.splitOn ".").foldl (fun n c => if !c.isEmpty && c.all Char.isDigit then .num n c.toNat! else .str n c) .anonymous

open Lean Meta Elab Term in
/-- `dropS% "T" i`: `drop0% T i` for a theorem given by its (possibly private) name. -/
elab "dropS% " T:str i:num : term => do
  let n := parseName T.getString
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
/-- `indepS% "T" i`: `indep0% T i` for a theorem given by its (possibly private) name. -/
elab "indepS% " T:str i:num : term => do
  let n := parseName T.getString
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
/-- `priv% "c"`: the constant `c` given by its (possibly private) name. -/
elab "priv% " c:str : term => do
  mkConstWithFreshMVarLevels (parseName c.getString)

open Lean Lake

namespace InternalLakeHand

/-! ## Match congruence lemmas -/

-- `Std.DTreeMap.Internal.Impl.get?.match_1.congr`: `ho`, with `o := .lt`, `o' := .gt`.
theorem getQ_ho : ¬ indep1% Std.DTreeMap.Internal.Impl.get?.match_1.congr 9 :=
  fun H => absurd (H (α := Nat) (o := .lt) (o' := .gt) (lt := fun _ => 0) (eq := fun _ => 0) (gt := fun _ => 0) (lt' := fun _ => 0) (eq' := fun _ => 0) (gt' := fun _ => 0)) (by decide)

-- `Std.DTreeMap.Internal.Impl.get?.match_1.congr`: `hlt`, with `o = o' = .lt` and branches `lt = 0`, `lt' = 1`.
theorem getQ_hlt : ¬ drop1% Std.DTreeMap.Internal.Impl.get?.match_1.congr 10 :=
  fun H => absurd (H (α := Nat) (o := .lt) (o' := .lt) (lt := fun _ => 0) (eq := fun _ => 0) (gt := fun _ => 0) (lt' := fun _ => 1) (eq' := fun _ => 0) (gt' := fun _ => 0) rfl (fun h => nomatch h) (fun h => nomatch h))
    (by decide)

-- `Std.DTreeMap.Internal.Impl.get?.match_1.congr`: `heq`, with `o = o' = .eq` and branches `eq = 0`, `eq' = 1`.
theorem getQ_heq : ¬ drop1% Std.DTreeMap.Internal.Impl.get?.match_1.congr 11 :=
  fun H => absurd (H (α := Nat) (o := .eq) (o' := .eq) (lt := fun _ => 0) (eq := fun _ => 0) (gt := fun _ => 0) (lt' := fun _ => 0) (eq' := fun _ => 1) (gt' := fun _ => 0) rfl (fun h => nomatch h) (fun h => nomatch h))
    (by decide)

-- `Std.DTreeMap.Internal.Impl.get?.match_1.congr`: `hgt`, with `o = o' = .gt` and branches `gt = 0`, `gt' = 1`.
theorem getQ_hgt : ¬ drop1% Std.DTreeMap.Internal.Impl.get?.match_1.congr 12 :=
  fun H => absurd (H (α := Nat) (o := .gt) (o' := .gt) (lt := fun _ => 0) (eq := fun _ => 0) (gt := fun _ => 0) (lt' := fun _ => 0) (eq' := fun _ => 0) (gt' := fun _ => 1) rfl (fun h => nomatch h) (fun h => nomatch h))
    (by decide)

-- `Std.DTreeMap.Internal.Impl.getEntryLE.match_1.congr`: `ho`, with `o := .lt`, `o' := .gt`.
theorem getEntryLE_ho : ¬ indep1% Std.DTreeMap.Internal.Impl.getEntryLE.match_1.congr 9 :=
  fun H => absurd (H (α := Nat) (o := .lt) (o' := .gt) (lt := fun _ => 0) (eq := fun _ => 0) (gt := fun _ => 0) (lt' := fun _ => 0) (eq' := fun _ => 0) (gt' := fun _ => 0)) (by decide)

-- `Std.DTreeMap.Internal.Impl.getEntryLE.match_1.congr`: `hlt`, with `o = o' = .lt` and branches `lt = 0`, `lt' = 1`.
theorem getEntryLE_hlt : ¬ drop1% Std.DTreeMap.Internal.Impl.getEntryLE.match_1.congr 10 :=
  fun H => absurd (H (α := Nat) (o := .lt) (o' := .lt) (lt := fun _ => 0) (eq := fun _ => 0) (gt := fun _ => 0) (lt' := fun _ => 1) (eq' := fun _ => 0) (gt' := fun _ => 0) rfl (fun h => nomatch h) (fun h => nomatch h))
    (by decide)

-- `Std.DTreeMap.Internal.Impl.getEntryLE.match_1.congr`: `heq`, with `o = o' = .eq` and branches `eq = 0`, `eq' = 1`.
theorem getEntryLE_heq : ¬ drop1% Std.DTreeMap.Internal.Impl.getEntryLE.match_1.congr 11 :=
  fun H => absurd (H (α := Nat) (o := .eq) (o' := .eq) (lt := fun _ => 0) (eq := fun _ => 0) (gt := fun _ => 0) (lt' := fun _ => 0) (eq' := fun _ => 1) (gt' := fun _ => 0) rfl (fun h => nomatch h) (fun h => nomatch h))
    (by decide)

-- `Std.DTreeMap.Internal.Impl.getEntryLE.match_1.congr`: `hgt`, with `o = o' = .gt` and branches `gt = 0`, `gt' = 1`.
theorem getEntryLE_hgt : ¬ drop1% Std.DTreeMap.Internal.Impl.getEntryLE.match_1.congr 12 :=
  fun H => absurd (H (α := Nat) (o := .gt) (o' := .gt) (lt := fun _ => 0) (eq := fun _ => 0) (gt := fun _ => 0) (lt' := fun _ => 0) (eq' := fun _ => 0) (gt' := fun _ => 1) rfl (fun h => nomatch h) (fun h => nomatch h))
    (by decide)

-- `Std.DTreeMap.Internal.Impl.entryAtIdx.match_1.congr`: `ho`, with `o := .lt`, `o' := .gt`.
theorem entryAtIdx_ho : ¬ indep1% Std.DTreeMap.Internal.Impl.entryAtIdx.match_1.congr 9 :=
  fun H => absurd (H (α := Nat) (o := .lt) (o' := .gt) (lt := fun _ => 0) (eq := fun _ => 0) (gt := fun _ => 0) (lt' := fun _ => 0) (eq' := fun _ => 0) (gt' := fun _ => 0)) (by decide)

-- `Std.DTreeMap.Internal.Impl.entryAtIdx.match_1.congr`: `hlt`, with `o = o' = .lt` and branches `lt = 0`, `lt' = 1`.
theorem entryAtIdx_hlt : ¬ drop1% Std.DTreeMap.Internal.Impl.entryAtIdx.match_1.congr 10 :=
  fun H => absurd (H (α := Nat) (o := .lt) (o' := .lt) (lt := fun _ => 0) (eq := fun _ => 0) (gt := fun _ => 0) (lt' := fun _ => 1) (eq' := fun _ => 0) (gt' := fun _ => 0) rfl (fun h => nomatch h) (fun h => nomatch h))
    (by decide)

-- `Std.DTreeMap.Internal.Impl.entryAtIdx.match_1.congr`: `heq`, with `o = o' = .eq` and branches `eq = 0`, `eq' = 1`.
theorem entryAtIdx_heq : ¬ drop1% Std.DTreeMap.Internal.Impl.entryAtIdx.match_1.congr 11 :=
  fun H => absurd (H (α := Nat) (o := .eq) (o' := .eq) (lt := fun _ => 0) (eq := fun _ => 0) (gt := fun _ => 0) (lt' := fun _ => 0) (eq' := fun _ => 1) (gt' := fun _ => 0) rfl (fun h => nomatch h) (fun h => nomatch h))
    (by decide)

-- `Std.DTreeMap.Internal.Impl.entryAtIdx.match_1.congr`: `hgt`, with `o = o' = .gt` and branches `gt = 0`, `gt' = 1`.
theorem entryAtIdx_hgt : ¬ drop1% Std.DTreeMap.Internal.Impl.entryAtIdx.match_1.congr 12 :=
  fun H => absurd (H (α := Nat) (o := .gt) (o' := .gt) (lt := fun _ => 0) (eq := fun _ => 0) (gt := fun _ => 0) (lt' := fun _ => 0) (eq' := fun _ => 0) (gt' := fun _ => 1) rfl (fun h => nomatch h) (fun h => nomatch h))
    (by decide)

-- `Std.DTreeMap.Internal.Impl.applyPartition.go.match_1.congr`: `ho`, with `o := .lt`, `o' := .gt`.
theorem applyPartition_go_ho : ¬ indep1% Std.DTreeMap.Internal.Impl.applyPartition.go.match_1.congr 9 :=
  fun H => absurd (H (α := Nat) (o := .lt) (o' := .gt) (lt := fun _ => 0) (eq := fun _ => 0) (gt := fun _ => 0) (lt' := fun _ => 0) (eq' := fun _ => 0) (gt' := fun _ => 0)) (by decide)

-- `Std.DTreeMap.Internal.Impl.applyPartition.go.match_1.congr`: `hlt`, with `o = o' = .lt` and branches `lt = 0`, `lt' = 1`.
theorem applyPartition_go_hlt : ¬ drop1% Std.DTreeMap.Internal.Impl.applyPartition.go.match_1.congr 10 :=
  fun H => absurd (H (α := Nat) (o := .lt) (o' := .lt) (lt := fun _ => 0) (eq := fun _ => 0) (gt := fun _ => 0) (lt' := fun _ => 1) (eq' := fun _ => 0) (gt' := fun _ => 0) rfl (fun h => nomatch h) (fun h => nomatch h))
    (by decide)

-- `Std.DTreeMap.Internal.Impl.applyPartition.go.match_1.congr`: `heq`, with `o = o' = .eq` and branches `eq = 0`, `eq' = 1`.
theorem applyPartition_go_heq : ¬ drop1% Std.DTreeMap.Internal.Impl.applyPartition.go.match_1.congr 11 :=
  fun H => absurd (H (α := Nat) (o := .eq) (o' := .eq) (lt := fun _ => 0) (eq := fun _ => 0) (gt := fun _ => 0) (lt' := fun _ => 0) (eq' := fun _ => 1) (gt' := fun _ => 0) rfl (fun h => nomatch h) (fun h => nomatch h))
    (by decide)

-- `Std.DTreeMap.Internal.Impl.applyPartition.go.match_1.congr`: `hgt`, with `o = o' = .gt` and branches `gt = 0`, `gt' = 1`.
theorem applyPartition_go_hgt : ¬ drop1% Std.DTreeMap.Internal.Impl.applyPartition.go.match_1.congr 12 :=
  fun H => absurd (H (α := Nat) (o := .gt) (o' := .gt) (lt := fun _ => 0) (eq := fun _ => 0) (gt := fun _ => 0) (lt' := fun _ => 0) (eq' := fun _ => 0) (gt' := fun _ => 1) rfl (fun h => nomatch h) (fun h => nomatch h))
    (by decide)

/-! ## Private Lake theorems -/

/-- A package with the given index and dependency indices. -/
noncomputable def pkg (i : Nat) (deps : Array Nat) : Package :=
  { (Classical.ofNonempty : Package) with wsIdx := i, depIdxs := deps }

/-- A workspace with one package (index 0, no dependencies). -/
noncomputable def raw1 : Workspace.Raw :=
  { (Classical.ofNonempty : Workspace.Raw) with packages := #[pkg 0 #[]] }

theorem raw1_wf : raw1.WF where
  size_packages_pos := by simp [raw1]
  packages_wsIdx {i} h := by
    simp [raw1] at h; subst h; simp [raw1, pkg]
  depIdxs_packages p hp i hi := by
    simp [raw1] at hp; subst hp; simp [pkg] at hi

/-- A well-formed workspace with one package. -/
noncomputable def ws1 : Workspace := ⟨raw1, raw1_wf⟩

-- _private.Lake.Load.Resolve.0.Lake.Workspace.size_packages_setDepIdxs (private, not checked by check_hand.py): `h`, with a package of index 5.
theorem size_packages_setDepIdxs_h :
    ¬ indepS% "_private.Lake.Load.Resolve.0.Lake.Workspace.size_packages_setDepIdxs" 3 :=
  fun H => absurd (H (ws := ws1) (pkg := pkg 5 #[]) (depIdxs := #[]) (h' := by simp)) (by simp [ws1, raw1, pkg])

-- _private.Lake.Load.Resolve.0.Lake.Workspace.size_packages_setDepIdxs (private, not checked by check_hand.py): `h'`, with dependency index 1.
theorem size_packages_setDepIdxs_h' :
    ¬ indepS% "_private.Lake.Load.Resolve.0.Lake.Workspace.size_packages_setDepIdxs" 4 :=
  fun H => absurd (H (ws := ws1) (pkg := pkg 0 #[]) (depIdxs := #[1]) (h := by simp [ws1, raw1, pkg]) 1 (by simp))
    (by simp [ws1, raw1, pkg])

-- _private.Lake.Load.Resolve.0.Lake.ResolveState.lt_of_mem (private, not checked by check_hand.py): `ResolveState.init ws1 0`, `i := ws.packages.size`.
theorem ResolveState_lt_of_mem_a :
    ¬ dropS% "_private.Lake.Load.Resolve.0.Lake.ResolveState.lt_of_mem" 3 := fun H =>
  let s := (priv% "_private.Lake.Load.Resolve.0.Lake.ResolveState.init") ws1 0
  Nat.lt_irrefl _ (H s _)

end InternalLakeHand
