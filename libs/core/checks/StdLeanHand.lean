import Lean.Elab.Command
-- add the library modules your rows need here (e.g. `import Init`, `import Std.Sat.AIG.CNF`); avoid `import Lean`/`import Std` (1.5 GB)
import Init
import Lake.Util.String
import Lean.ConstTrie
import Lean.Data.PersistentHashMap
import Lean.Data.RArray
import Lean.Elab.Tactic.Do.ProofMode.Cases
import Lean.Environment
import Std.Data.DHashMap.Internal.WF
import Std.Data.DHashMap.Lemmas
import Std.Data.DHashMap.RawLemmas
import Std.Data.DTreeMap.Internal.Lemmas
import Std.Data.DTreeMap.Internal.Zipper
import Std.Data.DTreeMap.Lemmas
import Std.Data.DTreeMap.Raw.Lemmas
import Std.Data.ExtDHashMap.Lemmas
import Std.Data.HashMap.Lemmas
import Std.Data.HashMap.RawLemmas
import Std.Data.HashSet.Lemmas
import Std.Data.HashSet.RawLemmas
import Std.Data.Internal.List.Associative
import Std.Data.Iterators.Combinators.Monadic.Drop
import Std.Data.Iterators.Lemmas.Equivalence.StepCongr
import Std.Data.TreeMap.Lemmas
import Std.Data.TreeMap.Raw.Lemmas
import Std.Data.TreeSet.Lemmas
import Std.Data.TreeSet.Raw.Lemmas
import Std.Do.Triple.SpecLemmas
import Std.Http.Data.URI.Encoding
import Std.Http.Internal.Char
import Std.Internal.ForIn.Lemmas
import Std.Internal.Order.Product
import Std.Time.Duration

/-!
Hand pass `StdLean` (hand22, 2026-11-08): 94 open hypotheses of private theorems in Std.Data
(DTreeMap/DHashMap internals, Internal.List, Iterators, map/set wrappers), Std.Do, Std.Http,
Std.Internal, Std.Time, Lean (ConstTrie, RArray, PersistentHashMap, Environment,
Elab.Tactic.Do) and Lake.Util. For hypothesis `hᵢ` of `T` each declaration proves `¬T'`
(`drop0% T i`), `¬ ∀ indep, Hᵢ` (`indep0% T i`, dependent rows) or `T'` (`drop% T i`).

90 necessary, 4 removable, 0 independent.

Reusable models (namespace `StdLeanHand`):
* `Ord` key models on type synonyms of `Nat` (with `OfNat`, `DecidableEq`): `CY` (cyclic
  `0 < 1 < 2 < 0`: oriented, not transitive), `E3` (`0 ~ 1` compare `.eq`, `1 < 2`, `2 < 0`:
  oriented, not transitive), `AL` (always `.lt`, `==` always false, `LawfulBEqOrd`), `GT` (always
  `.gt`), `NB` (`Nat` order with `TransOrd`, `==` always false, constant hash, `LawfulHashable`).
* Trees: `lf`, `nd k l r` (`Impl _ (fun _ => Nat)`), `tCY` (ordered `[0, 1]` under `CY`, with
  `tCY_ord`), `tUn` (unordered `[1, 0]` over `Nat`); range-iterator `toList` evaluation through the
  private library lemmas (`rxc_toList`, `rxo_toList`, `z_toList`) and then `decide`.
* ConstTrie: `ndC` (inner node with one leaf child), `xC` (that child, `xC_child`), `xN` (the node
  itself, `xN_not_child`).
* Iterators (copied from `checks/OpEHand.lean`): `YL` (yields forever, productive), `EM` (done),
  `LP` (skips to itself, `LP.not_productive`), `wf_irrefl`; `BM` (`Option` with `pure _ := none`,
  not lawful); `drop_rel_irrefl` (the private `Drop.ProductiveRel` is irreflexive).
* `eqn% c k`: the `k`-th equation lemma of a (private) definition, for unfolding well-founded or
  private definitions (`RArray.ofFn.go`, `Impl.pruneLE`).

Removable: `ofNanoseconds.mod_nonpos` (`b ≥ 0`), `not_quotedStringChar_ofNat_aux` (`c < 128`),
`Zipper.prependMap_pruneLE_eq_prependMapGE` (`ord_t`), `Zipper.prependMap_eq_prependMapGT_self`
(`ord_r`).

Run with the lean4 repo's stage1 binary: `runs/hand22/lean.sh checks/StdLeanHand.lean`.
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

open Std

open Lean Meta Elab Term in
/-- `eqn% c k`: the `k`-th equation lemma of the definition `c` (public, or private written as
`_private.Mod.«0».x`). -/
elab "eqn% " c:ident k:num : term => do
  let n ← hcConst c
  let some eqs ← getEqnsFor? n | throwError "no equation lemmas for {n}"
  mkConstWithFreshMVarLevels eqs[k.getNat]!

namespace StdLeanHand

-- `Lake.isValidChar_of_lt_256` (idx 1, necessary): n = 55296 (0xD800, a surrogate): not a valid char
theorem t_isValidChar : ¬ (drop0% _private.Lake.Util.String.«0».Lake.isValidChar_of_lt_256 1) :=
  fun H => absurd (H (n := 55296)) (by decide)

abbrev ndC : Lean.ConstTrie Nat := .inner .anonymous #[.leaf .anonymous 0]
abbrev xC : Nat × Lean.ConstTrie Nat := (0, .leaf .anonymous 0)
abbrev xN : Nat × Lean.ConstTrie Nat := (0, ndC)
theorem xC_child : (priv% _private.Lean.ConstTrie.«0».Lean.ImportedConsts.IsCandChild) #[(0, ndC)] xC.2 :=
  ⟨(0, ndC), by simp, by simp [Lean.ConstTrie.children]⟩
theorem xN_not_child : ¬ (priv% _private.Lean.ConstTrie.«0».Lean.ImportedConsts.IsCandChild) #[(0, ndC)] xN.2 := by
  rintro ⟨p, hp, hc⟩
  simp at hp; subst hp; simp [Lean.ConstTrie.children] at hc

-- `Lean.ImportedConsts.GroupsOk.modify` (idx 3, necessary): groups = #[#[]] (empty group), gi = 5 out of range, x a child of the only candidate
theorem t_modify_h : ¬ (drop0% _private.Lean.ConstTrie.«0».Lean.ImportedConsts.GroupsOk.modify 3) := fun H => by
  have := (H (cands := #[(0, ndC)]) (groups := #[#[]]) 5 xC xC_child #[] (by simp)).1
  simp at this

-- `Lean.ImportedConsts.GroupsOk.modify` (idx 6, necessary): cands = #[(0, inner [leaf])], groups = #[#[(0, leaf)]], gi = 0, x = (0, the candidate node itself), not a child
theorem t_modify_hx : ¬ (drop0% _private.Lean.ConstTrie.«0».Lean.ImportedConsts.GroupsOk.modify 6) := fun H => by
  have := H (cands := #[(0, ndC)]) (groups := #[#[xC]]) (fun g hg => by simp at hg; subst hg; exact ⟨by simp, fun x hx => by simp at hx; subst hx; exact xC_child⟩) 0 xN #[xC, xN] (by simp)
  exact xN_not_child (this.2 xN (by simp))

-- `Lean.ImportedConsts.GroupsOk.push` (idx 3, necessary): groups = #[#[]] (empty group), x a child of the only candidate
theorem t_push_h : ¬ (drop0% _private.Lean.ConstTrie.«0».Lean.ImportedConsts.GroupsOk.push 3) := fun H => by
  have := (H (cands := #[(0, ndC)]) (groups := #[#[]]) xC xC_child #[] (by simp)).1
  simp at this

-- `Lean.ImportedConsts.GroupsOk.push` (idx 5, necessary): groups = #[], x = (0, the candidate node itself), not a child
theorem t_push_hx : ¬ (drop0% _private.Lean.ConstTrie.«0».Lean.ImportedConsts.GroupsOk.push 5) := fun H => by
  have := H (cands := #[(0, ndC)]) (groups := #[]) (fun g hg => by simp at hg) xN #[xN] (by simp)
  exact xN_not_child (this.2 xN (by simp))

-- `Lean.ImportedConsts.le_maxSize` (idx 3, necessary): cands = #[], p = (0, leaf): sizeOf leaf = 2 > maxSize #[] = 0
theorem t_le_maxSize : ¬ (drop0% _private.Lean.ConstTrie.«0».Lean.ImportedConsts.le_maxSize 3) := fun H => by
  have := H (p := xC) (cands := #[])
  exact absurd this (by decide)

-- `Lean.ImportedConsts.maxSize_lt` (idx 4, necessary): g = #[(0, leaf)], cands = #[]: maxSize g > 0 = maxSize cands
theorem t_maxSize_lt : ¬ (drop0% _private.Lean.ConstTrie.«0».Lean.ImportedConsts.maxSize_lt 4) := fun H => by
  exact Nat.not_lt_zero _ (H (g := #[xC]) (cands := #[]) (by decide))

-- `Lean.ImportedConsts.sizeOf_lt_of_mem_children` (idx 3, necessary): t = c: sizeOf c < sizeOf c fails
theorem t_sizeOf_lt : ¬ (drop0% _private.Lean.ConstTrie.«0».Lean.ImportedConsts.sizeOf_lt_of_mem_children 3) :=
  fun H => Nat.lt_irrefl _ (H (t := ndC) (c := ndC))

-- `Lean.PersistentHashMap.size_set` (idx 4, necessary): ks = #[0], vs = #[0, 0], i = j = 0: sizes 1 and 2
theorem t_size_set : ¬ (drop0% _private.Lean.Data.PersistentHashMap.«0».Lean.PersistentHashMap.size_set 4) := fun H => by
  have := H (ks := #[0]) (vs := #[0, 0]) 0 0 0 0
  simp at this

-- `Lean.RArray.get_ofFn.go` (idx 8, necessary): n = 2, f = val, i = 0, lb = 1, ub = 2: go is leaf (f 1), get 0 = 1 != 0
theorem t_rarray8 : ¬ (drop0% _private.Lean.Data.RArray.«0».Lean.RArray.get_ofFn.go 8) := fun H => by
  have := H (n := 2) (fun i => i.val) 0 1 2 (by decide) (by decide) (by decide)
  rw [eqn% _private.Lean.Data.RArray.«0».Lean.RArray.ofFn.go 0] at this
  simp [Lean.RArray.get] at this

-- `Lean.Elab.Tactic.Do.ProofMode.assembled_proof` (idx 7, necessary): sigma = [], P = True, all others False
theorem t_assembled7 : ¬ (drop0% _private.Lean.Elab.Tactic.Do.ProofMode.Cases.«0».Lean.Elab.Tactic.Do.ProofMode.assembled_proof 7) := fun H =>
  H (σs := []) (P := ⟨True⟩) (P' := ⟨False⟩) (Q := ⟨False⟩) (H := ⟨False⟩) (H' := ⟨False⟩) (T := ⟨False⟩)
    (by simp) (by simp) (by simp) trivial

-- `Lean.instNonemptyVisibilityMap` (idx 1, necessary): alpha = Empty: VisibilityMap Empty is empty
theorem t_visMap : ¬ (drop0% _private.Lean.Environment.«0».Lean.instNonemptyVisibilityMap 1) := fun H => by
  obtain ⟨v⟩ := @H Empty
  cases v
  rename_i a _
  exact a.elim

end StdLeanHand

open Std Std.DTreeMap.Internal

namespace StdLeanHand

/-! Key models for `Ord`-based rows. -/

/-- `CY`: keys compared cyclically mod 3 (`0 < 1 < 2 < 0`): oriented, not transitive. -/
def CY := Nat
instance (n : Nat) : OfNat CY n := ⟨(n : Nat)⟩
instance : DecidableEq CY := inferInstanceAs (DecidableEq Nat)
def cyc (a b : Nat) : Ordering :=
  if a % 3 = b % 3 then .eq else if (a + 1) % 3 = b % 3 then .lt else .gt
instance : Ord CY := ⟨cyc⟩

/-- `E3`: `0 ~ 1` (`.eq`), `1 < 2`, `2 < 0`: oriented, not transitive. -/
def E3 := Nat
instance (n : Nat) : OfNat E3 n := ⟨(n : Nat)⟩
instance : DecidableEq E3 := inferInstanceAs (DecidableEq Nat)
def e3 : Nat → Nat → Ordering
  | 0, 1 => .eq | 1, 0 => .eq | 1, 2 => .lt | 2, 1 => .gt | 0, 2 => .gt | 2, 0 => .lt
  | a, b => compare a b
instance : Ord E3 := ⟨e3⟩

/-- `AL`: everything compares `.lt`, `==` is always false (`LawfulBEqOrd`, not oriented). -/
def AL := Nat
instance (n : Nat) : OfNat AL n := ⟨(n : Nat)⟩
instance : DecidableEq AL := inferInstanceAs (DecidableEq Nat)
instance : Ord AL := ⟨fun _ _ => .lt⟩
instance : BEq AL := ⟨fun _ _ => false⟩
instance : LawfulBEqOrd AL := ⟨by intro a b; simp [compare, BEq.beq]⟩

/-- `GT`: everything compares `.gt`. -/
def GT := Nat
instance (n : Nat) : OfNat GT n := ⟨(n : Nat)⟩
instance : DecidableEq GT := inferInstanceAs (DecidableEq Nat)
instance : Ord GT := ⟨fun _ _ => .gt⟩

/-- `NB`: `Nat` order, `==` always false (lawful order, `LawfulBEqOrd` fails). -/
def NB := Nat
instance (n : Nat) : OfNat NB n := ⟨(n : Nat)⟩
instance : DecidableEq NB := inferInstanceAs (DecidableEq Nat)
instance : Ord NB := inferInstanceAs (Ord Nat)
instance : TransOrd NB := inferInstanceAs (TransOrd Nat)
instance : BEq NB := ⟨fun _ _ => false⟩
instance : Hashable NB := ⟨fun _ => 0⟩
instance : LawfulHashable NB := ⟨fun _ _ h => Bool.noConfusion h⟩

/-! Associative-list rows. -/

-- `Std.Internal.List.antisymm_subtype` (idx 3, necessary): model AL (compare always lt, == always false): keys 0 and 1 are <= both ways
theorem t_antisymm3 : ¬ (drop0% _private.Std.Data.Internal.List.Associative.«0».Std.Internal.List.antisymm_subtype 3) := fun H => by
  have h := @H AL (fun _ => Nat) _ _ _ [⟨0, 0⟩, ⟨1, 0⟩] ⟨by simp [Std.Internal.List.keys, BEq.beq]⟩
  have := h.antisymm ⟨⟨0, 0⟩, by simp⟩ ⟨⟨1, 0⟩, by simp⟩ (by decide) (by decide)
  simp at this

-- `Std.Internal.List.antisymm_subtype` (idx 5, necessary): model NB (Nat order, == always false): l = [(0,0),(0,1)] has distinct keys
theorem t_antisymm5 : ¬ (drop0% _private.Std.Data.Internal.List.Associative.«0».Std.Internal.List.antisymm_subtype 5) := fun H => by
  have h := @H NB (fun _ => Nat) _ _ _ [⟨0, 0⟩, ⟨0, 1⟩] ⟨by simp [Std.Internal.List.keys, BEq.beq]⟩
  have := h.antisymm ⟨⟨0, 0⟩, by simp⟩ ⟨⟨0, 1⟩, by simp⟩ (by decide) (by decide)
  simp at this

-- `Std.Internal.List.antisymm_subtype` (idx 7, necessary): Nat, l = [(0,0),(0,1)] (duplicate key)
theorem t_antisymm7 : ¬ (drop0% _private.Std.Data.Internal.List.Associative.«0».Std.Internal.List.antisymm_subtype 7) := fun H => by
  have h := @H Nat (fun _ => Nat) _ _ _ _ [⟨0, 0⟩, ⟨0, 1⟩]
  have := h.antisymm ⟨⟨0, 0⟩, by simp⟩ ⟨⟨0, 1⟩, by simp⟩ (by decide) (by decide)
  simp at this

-- `Std.Internal.List.instAssociativeSigmaMinOfTransOrd_std` (idx 3, necessary): model CY (cyclic 0<1<2<0): min (min 0 1) 2 = 2, min 0 (min 1 2) = 0
theorem t_assoc : ¬ (drop0% _private.Std.Data.Internal.List.Associative.«0».Std.Internal.List.instAssociativeSigmaMinOfTransOrd_std 3) := fun H => by
  have := (@H CY (fun _ => Nat) _).assoc ⟨0, 0⟩ ⟨1, 0⟩ ⟨2, 0⟩
  revert this; decide

-- `Std.Internal.List.leSigmaOfOrd_total` (idx 3, necessary): model GT (compare always gt): a <= a fails
theorem t_total : ¬ (drop0% _private.Std.Data.Internal.List.Associative.«0».Std.Internal.List.leSigmaOfOrd_total 3) := fun H => by
  have := @H GT (fun _ => Nat) _ ⟨0, 0⟩ ⟨0, 0⟩
  revert this; decide

-- `Std.Internal.List.le_min_iff` (idx 3, necessary): model CY: a = 0, b = 1, c = 2
theorem t_le_min : ¬ (drop0% _private.Std.Data.Internal.List.Associative.«0».Std.Internal.List.le_min_iff 3) := fun H => by
  have := @H CY (fun _ => Nat) _ ⟨0, 0⟩ ⟨1, 0⟩ ⟨2, 0⟩
  revert this; decide

-- `Std.Internal.List.minEntry?_cons` (idx 3, necessary): model CY: e = 0, l = [1, 2]
theorem t_minEntry : ¬ (drop0% _private.Std.Data.Internal.List.Associative.«0».Std.Internal.List.minEntry?_cons 3) := fun H => by
  have := @H CY (fun _ => Nat) _ ⟨0, 0⟩ [⟨1, 0⟩, ⟨2, 0⟩]
  revert this; decide

-- `Std.Internal.List.min_apply` (idx 6, necessary): Nat, e1 = 0, e2 = 1, f swaps keys 0 and 1
theorem t_min_apply : ¬ (drop0% _private.Std.Data.Internal.List.Associative.«0».Std.Internal.List.min_apply 6) := fun H => by
  have := @H Nat (fun _ => Nat) _ ⟨0, 0⟩ ⟨1, 0⟩ (fun e => ⟨1 - e.1, e.2⟩)
  revert this; decide

-- `Std.Internal.List.Option.dmap_congr` (idx 4, necessary): dependent; o = none, o' = some 0
theorem t_dmap_ho : ¬ (indep0% _private.Std.Data.Internal.List.Associative.«0».Std.Internal.List.Option.dmap_congr 4) := fun H => by
  have := @H Nat Nat none (some 0) (fun _ _ => 0) (fun _ _ => 0)
  simp at this

-- `Std.Internal.List.Option.dmap_congr` (idx 7, necessary): o = o' = some 0, f = 0, f' = 1
theorem t_dmap_hf : ¬ (drop0% _private.Std.Data.Internal.List.Associative.«0».Std.Internal.List.Option.dmap_congr 7) := fun H => by
  have := @H Nat Nat (some 0) (some 0) rfl (fun _ _ => 0) (fun _ _ => 1)
  revert this; decide

-- `Std.Internal.List.Option.get_dmap` (idx 4, necessary): dependent; x = none
theorem t_get_dmap : ¬ (indep0% _private.Std.Data.Internal.List.Associative.«0».Std.Internal.List.Option.get_dmap 4) := fun H => by
  have := @H Nat Nat none (fun _ _ => 0)
  revert this; decide

-- `Std.Internal.List.Option.pmap_eq_dmap` (idx 5, necessary): dependent; p = False, x = some 0
theorem t_pmap_dmap : ¬ (indep0% _private.Std.Data.Internal.List.Associative.«0».Std.Internal.List.Option.pmap_eq_dmap 5) := fun H =>
  @H Nat Nat (fun _ => False) (some 0) (fun _ h => h.elim) 0 rfl

-- `Std.Internal.List.Option.map_cast_apply` (idx 2, necessary): dependent; gamma = Bool, gamma' = Empty
theorem t_mapcast_list : ¬ (indep0% _private.Std.Data.Internal.List.Associative.«0».Std.Internal.List.Option.map_cast_apply 2) :=
  fun H => (cast (@H Bool Empty none) true).elim
-- `Std.DHashMap.Option.map_cast_apply` (idx 2, necessary): dependent; gamma = Bool, gamma' = Empty
theorem t_mapcast_dhm : ¬ (indep0% _private.Std.Data.DHashMap.Lemmas.«0».Std.DHashMap.Option.map_cast_apply 2) :=
  fun H => (cast (@H Bool Empty none) true).elim
-- `Std.DHashMap.Raw.Option.map_cast_apply` (idx 2, necessary): dependent; gamma = Bool, gamma' = Empty
theorem t_mapcast_dhmraw : ¬ (indep0% _private.Std.Data.DHashMap.RawLemmas.«0».Std.DHashMap.Raw.Option.map_cast_apply 2) :=
  fun H => (cast (@H Bool Empty none) true).elim
-- `Std.DTreeMap.Internal.Impl.Option.map_cast_apply` (idx 2, necessary): dependent; gamma = Bool, gamma' = Empty
theorem t_mapcast_impl : ¬ (indep0% _private.Std.Data.DTreeMap.Internal.Lemmas.«0».Std.DTreeMap.Internal.Impl.Option.map_cast_apply 2) :=
  fun H => (cast (@H Bool Empty none) true).elim

/-! Map/set wrappers: `t.inner = t'.inner → t = t'` dropped. -/

-- `Std.DHashMap.ext` (idx 6, necessary): empty map vs. insert 0 0 (isEmpty differs)
theorem t_ext_dhm : ¬ (drop0% _private.Std.Data.DHashMap.Lemmas.«0».Std.DHashMap.ext 6) := fun H => by
  have := congrArg DHashMap.isEmpty (@H Nat (fun _ => Nat) _ _ ∅ ((∅ : DHashMap Nat fun _ => Nat).insert 0 0))
  simp at this
-- `Std.HashMap.ext` (idx 6, necessary): empty map vs. insert 0 0 (isEmpty differs)
theorem t_ext_hm : ¬ (drop0% _private.Std.Data.HashMap.Lemmas.«0».Std.HashMap.ext 6) := fun H => by
  have := congrArg HashMap.isEmpty (@H Nat Nat _ _ ∅ ((∅ : HashMap Nat Nat).insert 0 0))
  simp at this
-- `Std.HashSet.ext` (idx 5, necessary): empty set vs. insert 0 (isEmpty differs)
theorem t_ext_hs : ¬ (drop0% _private.Std.Data.HashSet.Lemmas.«0».Std.HashSet.ext 5) := fun H => by
  have := congrArg HashSet.isEmpty (@H Nat _ _ ∅ ((∅ : HashSet Nat).insert 0))
  simp at this
-- `Std.HashMap.Raw.ext` (idx 4, necessary): raw maps with size fields 0 and 1
theorem t_ext_hmraw : ¬ (drop0% _private.Std.Data.HashMap.RawLemmas.«0».Std.HashMap.Raw.ext 4) := fun H => by
  have := @H Nat Nat ⟨⟨0, #[]⟩⟩ ⟨⟨1, #[]⟩⟩
  cases this
-- `Std.HashSet.Raw.ext` (idx 3, necessary): raw sets with size fields 0 and 1
theorem t_ext_hsraw : ¬ (drop0% _private.Std.Data.HashSet.RawLemmas.«0».Std.HashSet.Raw.ext 3) := fun H => by
  have := @H Nat ⟨⟨⟨0, #[]⟩⟩⟩ ⟨⟨⟨1, #[]⟩⟩⟩
  cases this
-- `Std.DTreeMap.ext` (idx 5, necessary): empty map vs. insert 0 0 (isEmpty differs)
theorem t_ext_dtm : ¬ (drop0% _private.Std.Data.DTreeMap.Lemmas.«0».Std.DTreeMap.ext 5) := fun H => by
  have := congrArg DTreeMap.isEmpty (@H Nat (fun _ => Nat) compare ∅ ((∅ : DTreeMap Nat (fun _ => Nat) compare).insert 0 0))
  simp at this
-- `Std.TreeMap.ext` (idx 5, necessary): empty map vs. insert 0 0 (isEmpty differs)
theorem t_ext_tm : ¬ (drop0% _private.Std.Data.TreeMap.Lemmas.«0».Std.TreeMap.ext 5) := fun H => by
  have := congrArg TreeMap.isEmpty (@H Nat Nat compare ∅ ((∅ : TreeMap Nat Nat compare).insert 0 0))
  simp at this
-- `Std.TreeSet.ext` (idx 4, necessary): empty set vs. insert 0 (isEmpty differs)
theorem t_ext_ts : ¬ (drop0% _private.Std.Data.TreeSet.Lemmas.«0».Std.TreeSet.ext 4) := fun H => by
  have := congrArg TreeSet.isEmpty (@H Nat compare ∅ ((∅ : TreeSet Nat compare).insert 0))
  simp at this
-- `Std.DTreeMap.Raw.ext` (idx 5, necessary): raw trees leaf vs. inner node
theorem t_ext_dtmraw : ¬ (drop0% _private.Std.Data.DTreeMap.Raw.Lemmas.«0».Std.DTreeMap.Raw.ext 5) := fun H => by
  have := @H Nat (fun _ => Nat) compare ⟨.leaf⟩ ⟨.inner 1 0 0 .leaf .leaf⟩
  cases this
-- `Std.TreeMap.Raw.ext` (idx 5, necessary): raw trees leaf vs. inner node
theorem t_ext_tmraw : ¬ (drop0% _private.Std.Data.TreeMap.Raw.Lemmas.«0».Std.TreeMap.Raw.ext 5) := fun H => by
  have := @H Nat Nat compare ⟨⟨.leaf⟩⟩ ⟨⟨.inner 1 0 0 .leaf .leaf⟩⟩
  cases this
-- `Std.TreeSet.Raw.ext` (idx 4, necessary): raw trees leaf vs. inner node
theorem t_ext_tsraw : ¬ (drop0% _private.Std.Data.TreeSet.Raw.Lemmas.«0».Std.TreeSet.Raw.ext 4) := fun H => by
  have := @H Nat compare ⟨⟨⟨.leaf⟩⟩⟩ ⟨⟨⟨.inner 1 0 () .leaf .leaf⟩⟩⟩
  cases this

end StdLeanHand

open Std Std.DTreeMap.Internal

namespace StdLeanHand

abbrev lf {α : Type} : Impl α (fun _ => Nat) := .leaf
abbrev nd {α : Type} (k : α) (l r : Impl α (fun _ => Nat)) : Impl α (fun _ => Nat) := .inner 1 k 0 l r

/-- `[0, 1]` under `CY`: ordered (`0 < 1`) but `2` is below `0` and above `1`. -/
abbrev tCY : Impl CY (fun _ => Nat) := nd 1 (nd 0 lf lf) lf
theorem tCY_ord : tCY.Ordered := by unfold Impl.Ordered; decide

-- `Std.DTreeMap.Internal.Impl.toList_pruneLE` (idx 3, necessary): model CY: tree [0, 1], lowerBound 2: prune gives [], filter gives [0]
theorem t_pruneLE : ¬ (drop0% _private.Std.Data.DTreeMap.Internal.Zipper.«0».Std.DTreeMap.Internal.Impl.toList_pruneLE 3) := fun H => by
  have := @H CY (fun _ => Nat) _ tCY tCY_ord 2
  revert this; decide

-- `Std.DTreeMap.Internal.Impl.toList_pruneLT` (idx 3, necessary): model CY: tree [0, 1], lowerBound 2: prune gives [], filter gives [0]
theorem t_pruneLT : ¬ (drop0% _private.Std.Data.DTreeMap.Internal.Zipper.«0».Std.DTreeMap.Internal.Impl.toList_pruneLT 3) := fun H => by
  have := @H CY (fun _ => Nat) _ tCY tCY_ord 2
  revert this; decide

-- `Std.DTreeMap.Internal.RxcIterator.step_cons_of_LE` (idx 8, necessary): Nat, k = 1, upper = 0: step is done
theorem t_step_LE : ¬ (drop0% _private.Std.Data.DTreeMap.Internal.Zipper.«0».Std.DTreeMap.Internal.RxcIterator.step_cons_of_LE 8) := fun H => by
  have := @H Nat (fun _ => Nat) 1 0 lf .done _ 0
  simp [RxcIterator.step] at this; exact this (by decide)

-- `Std.DTreeMap.Internal.RxcIterator.step_cons_of_not_LE` (idx 8, necessary): Nat, k = 0, upper = 0: step yields
theorem t_step_notLE : ¬ (drop0% _private.Std.Data.DTreeMap.Internal.Zipper.«0».Std.DTreeMap.Internal.RxcIterator.step_cons_of_not_LE 8) := fun H => by
  have := @H Nat (fun _ => Nat) 0 0 lf .done _ 0
  simp [RxcIterator.step] at this

-- `Std.DTreeMap.Internal.RxoIterator.step_cons_of_isLT` (idx 8, necessary): Nat, k = 0, upper = 0: step is done
theorem t_step_LT : ¬ (drop0% _private.Std.Data.DTreeMap.Internal.Zipper.«0».Std.DTreeMap.Internal.RxoIterator.step_cons_of_isLT 8) := fun H => by
  have := @H Nat (fun _ => Nat) 0 0 lf .done _ 0
  simp [RxoIterator.step] at this

-- `Std.DTreeMap.Internal.RxoIterator.step_cons_of_isLT_eq_false` (idx 8, necessary): Nat, k = 0, upper = 1: step yields
theorem t_step_notLT : ¬ (drop0% _private.Std.Data.DTreeMap.Internal.Zipper.«0».Std.DTreeMap.Internal.RxoIterator.step_cons_of_isLT_eq_false 8) := fun H => by
  have := @H Nat (fun _ => Nat) 0 0 lf .done _ 1
  simp [RxoIterator.step] at this; exact this (by decide)

-- `Std.DTreeMap.Internal.RxcIterator.takeWhile_eq_filter` (idx 3, necessary): model CY: l = [0, 1], bound 2
theorem t_tw_rxc_inst : ¬ (drop0% _private.Std.Data.DTreeMap.Internal.Zipper.«0».Std.DTreeMap.Internal.RxcIterator.takeWhile_eq_filter 3) := fun H => by
  have := @H CY (fun _ => Nat) _ 2 [⟨0, 0⟩, ⟨1, 0⟩] (by decide)
  revert this; decide

-- `Std.DTreeMap.Internal.RxcIterator.takeWhile_eq_filter` (idx 6, necessary): Nat: l = [1, 0], bound 0
theorem t_tw_rxc_ord : ¬ (drop0% _private.Std.Data.DTreeMap.Internal.Zipper.«0».Std.DTreeMap.Internal.RxcIterator.takeWhile_eq_filter 6) := fun H => by
  have := @H Nat (fun _ => Nat) _ _ 0 [⟨1, 0⟩, ⟨0, 0⟩]
  revert this; decide

-- `Std.DTreeMap.Internal.RxoIterator.takeWhile_eq_filter` (idx 3, necessary): model CY: l = [0, 1], bound 2
theorem t_tw_rxo_inst : ¬ (drop0% _private.Std.Data.DTreeMap.Internal.Zipper.«0».Std.DTreeMap.Internal.RxoIterator.takeWhile_eq_filter 3) := fun H => by
  have := @H CY (fun _ => Nat) _ 2 [⟨0, 0⟩, ⟨1, 0⟩] (by decide)
  revert this; decide

-- `Std.DTreeMap.Internal.RxoIterator.takeWhile_eq_filter` (idx 6, necessary): Nat: l = [1, 0], bound 1
theorem t_tw_rxo_ord : ¬ (drop0% _private.Std.Data.DTreeMap.Internal.Zipper.«0».Std.DTreeMap.Internal.RxoIterator.takeWhile_eq_filter 6) := fun H => by
  have := @H Nat (fun _ => Nat) _ _ 1 [⟨1, 0⟩, ⟨0, 0⟩]
  revert this; decide

-- `Std.DTreeMap.Internal.Zipper.ordered_of_ordered_cons` (idx 8, necessary): Nat: z with toList [1, 0]
theorem t_ord_cons : ¬ (drop0% _private.Std.Data.DTreeMap.Internal.Zipper.«0».Std.DTreeMap.Internal.Zipper.ordered_of_ordered_cons 8) := fun H => by
  have := @H Nat (fun _ => Nat) 0 0 _ _ lf (.cons 1 0 lf (.cons 0 0 lf .done))
  revert this; unfold Zipper.Ordered; decide

-- `Std.DTreeMap.Internal.Zipper.ordered_prependMap` (idx 7, necessary): Nat: t = leaf, z with toList [1, 0]
theorem t_ordPM_z : ¬ (drop0% _private.Std.Data.DTreeMap.Internal.Zipper.«0».Std.DTreeMap.Internal.Zipper.ordered_prependMap 7) := fun H => by
  have := @H Nat (fun _ => Nat) _ _ lf (by unfold Impl.Ordered; decide) (.cons 1 0 lf (.cons 0 0 lf .done)) (by simp)
  revert this; unfold Zipper.Ordered; decide

-- `Std.DTreeMap.Internal.Zipper.ordered_prependMap` (idx 8, necessary): Nat: t = [0], z = [0]: result [0, 0]
theorem t_ordPM_hyp : ¬ (drop0% _private.Std.Data.DTreeMap.Internal.Zipper.«0».Std.DTreeMap.Internal.Zipper.ordered_prependMap 8) := fun H => by
  have := @H Nat (fun _ => Nat) _ _ (nd 0 lf lf) (by unfold Impl.Ordered; decide) (.cons 0 0 lf .done) (by unfold Zipper.Ordered; decide)
  revert this; unfold Zipper.Ordered; decide

-- `Std.DTreeMap.Internal.Zipper.prependMap_eq_prependMapGT_self` (idx 8, necessary): Nat: r = [0], lowerBound 0
theorem t_PMGT_hyp : ¬ (drop0% _private.Std.Data.DTreeMap.Internal.Zipper.«0».Std.DTreeMap.Internal.Zipper.prependMap_eq_prependMapGT_self 8) := fun H => by
  have := @H Nat (fun _ => Nat) _ _ (nd 0 lf lf) .done 0 (by unfold Impl.Ordered; decide)
  have := congrArg Zipper.toList this
  revert this; decide

-- `Std.DTreeMap.Internal.Zipper.prependMap_pruneLT_eq_prependMapGT` (idx 3, necessary): model E3 (0 ~ 1, 1 < 2, 2 < 0): t = [1, 2], lowerBound 0
theorem t_pruneLT_PMGT_inst : ¬ (drop0% _private.Std.Data.DTreeMap.Internal.Zipper.«0».Std.DTreeMap.Internal.Zipper.prependMap_pruneLT_eq_prependMapGT 3) := fun H => by
  have := @H E3 (fun _ => Nat) _ (nd 1 lf (nd 2 lf lf)) (by unfold Impl.Ordered; decide) .done 0
  have := congrArg Zipper.toList this
  revert this; decide

-- `Std.DTreeMap.Internal.Zipper.prependMap_pruneLT_eq_prependMapGT` (idx 5, necessary): Nat: unordered t = [0, 0], lowerBound 0
theorem t_pruneLT_PMGT_ord : ¬ (drop0% _private.Std.Data.DTreeMap.Internal.Zipper.«0».Std.DTreeMap.Internal.Zipper.prependMap_pruneLT_eq_prependMapGT 5) := fun H => by
  have := @H Nat (fun _ => Nat) _ _ (nd 0 lf (nd 0 lf lf)) .done 0
  have := congrArg Zipper.toList this
  revert this; decide

/-! Range iterators over a tree. -/

theorem rxc_toList {α : Type} [Ord α] (z : Zipper α (fun _ => Nat)) (b : α) :
    (⟨RxcIterator.mk z b⟩ : Iter (Sigma (fun _ : α => Nat))).toList = z.toList.takeWhile (fun e => (compare e.fst b).isLE) :=
  (priv% _private.Std.Data.DTreeMap.Internal.Zipper.«0».Std.DTreeMap.Internal.RxcIterator.toList_rxcIter) (z := z) (bound := b)
theorem rxo_toList {α : Type} [Ord α] (z : Zipper α (fun _ => Nat)) (b : α) :
    (⟨RxoIterator.mk z b⟩ : Iter (Sigma (fun _ : α => Nat))).toList = z.toList.takeWhile (fun e => (compare e.fst b).isLT) :=
  (priv% _private.Std.Data.DTreeMap.Internal.Zipper.«0».Std.DTreeMap.Internal.RxoIterator.toList_rxoIter) (z := z) (bound := b)
theorem z_toList {α : Type} (z : Zipper α (fun _ => Nat)) :
    (⟨z⟩ : Iter (α := Zipper α (fun _ => Nat)) (Sigma (fun _ : α => Nat))).toList = z.toList :=
  (priv% _private.Std.Data.DTreeMap.Internal.Zipper.«0».Std.DTreeMap.Internal.Zipper.toList_iter) (z := z)

/-- `[1, 0]`: not ordered. -/
abbrev tUn : Impl Nat (fun _ => Nat) := nd 0 (nd 1 lf lf) lf

-- `Std.DTreeMap.Internal.toList_rccIter` (idx 3, necessary): model CY: tree [0, 1], bounds 2 and 1
theorem t_rcc_inst : ¬ (drop0% _private.Std.Data.DTreeMap.Internal.Zipper.«0».Std.DTreeMap.Internal.toList_rccIter 3) := fun H => by
  have := @H CY (fun _ => Nat) _ tCY tCY_ord 2 1
  rw [rccIterator, rxc_toList] at this; revert this; decide
-- `Std.DTreeMap.Internal.toList_rccIter` (idx 5, necessary): Nat: unordered tree [1, 0], bounds 1 and 5
theorem t_rcc_ord : ¬ (drop0% _private.Std.Data.DTreeMap.Internal.Zipper.«0».Std.DTreeMap.Internal.toList_rccIter 5) := fun H => by
  have := @H Nat (fun _ => Nat) _ _ tUn 1 5
  rw [rccIterator, rxc_toList] at this; revert this; decide
-- `Std.DTreeMap.Internal.toList_rcoIter` (idx 3, necessary): model CY: tree [0, 1], bounds 2 and 1
theorem t_rco_inst : ¬ (drop0% _private.Std.Data.DTreeMap.Internal.Zipper.«0».Std.DTreeMap.Internal.toList_rcoIter 3) := fun H => by
  have := @H CY (fun _ => Nat) _ tCY tCY_ord 2 1
  rw [rcoIterator, rxo_toList] at this; revert this; decide
-- `Std.DTreeMap.Internal.toList_rcoIter` (idx 5, necessary): Nat: unordered tree [1, 0], bounds 1 and 5
theorem t_rco_ord : ¬ (drop0% _private.Std.Data.DTreeMap.Internal.Zipper.«0».Std.DTreeMap.Internal.toList_rcoIter 5) := fun H => by
  have := @H Nat (fun _ => Nat) _ _ tUn 1 5
  rw [rcoIterator, rxo_toList] at this; revert this; decide
-- `Std.DTreeMap.Internal.toList_rocIter` (idx 3, necessary): model CY: tree [0, 1], bounds 2 and 1
theorem t_roc_inst : ¬ (drop0% _private.Std.Data.DTreeMap.Internal.Zipper.«0».Std.DTreeMap.Internal.toList_rocIter 3) := fun H => by
  have := @H CY (fun _ => Nat) _ tCY tCY_ord 2 1
  rw [rocIterator, rxc_toList] at this; revert this; decide
-- `Std.DTreeMap.Internal.toList_rocIter` (idx 5, necessary): Nat: unordered tree [1, 0], bounds 0 and 5
theorem t_roc_ord : ¬ (drop0% _private.Std.Data.DTreeMap.Internal.Zipper.«0».Std.DTreeMap.Internal.toList_rocIter 5) := fun H => by
  have := @H Nat (fun _ => Nat) _ _ tUn 0 5
  rw [rocIterator, rxc_toList] at this; revert this; decide
-- `Std.DTreeMap.Internal.toList_rooIter` (idx 3, necessary): model CY: tree [0, 1], bounds 2 and 1
theorem t_roo_inst : ¬ (drop0% _private.Std.Data.DTreeMap.Internal.Zipper.«0».Std.DTreeMap.Internal.toList_rooIter 3) := fun H => by
  have := @H CY (fun _ => Nat) _ tCY tCY_ord 2 1
  rw [rooIterator, rxo_toList] at this; revert this; decide
-- `Std.DTreeMap.Internal.toList_rooIter` (idx 5, necessary): Nat: unordered tree [1, 0], bounds 0 and 5
theorem t_roo_ord : ¬ (drop0% _private.Std.Data.DTreeMap.Internal.Zipper.«0».Std.DTreeMap.Internal.toList_rooIter 5) := fun H => by
  have := @H Nat (fun _ => Nat) _ _ tUn 0 5
  rw [rooIterator, rxo_toList] at this; revert this; decide
-- `Std.DTreeMap.Internal.toList_rciIter` (idx 3, necessary): model CY: tree [0, 1], lowerBound 2
theorem t_rci_inst : ¬ (drop0% _private.Std.Data.DTreeMap.Internal.Zipper.«0».Std.DTreeMap.Internal.toList_rciIter 3) := fun H => by
  have := @H CY (fun _ => Nat) _ tCY tCY_ord 2
  rw [rciIterator, z_toList] at this; revert this; decide
-- `Std.DTreeMap.Internal.toList_rciIter` (idx 5, necessary): Nat: unordered tree [1, 0], lowerBound 1
theorem t_rci_ord : ¬ (drop0% _private.Std.Data.DTreeMap.Internal.Zipper.«0».Std.DTreeMap.Internal.toList_rciIter 5) := fun H => by
  have := @H Nat (fun _ => Nat) _ _ tUn 1
  rw [rciIterator, z_toList] at this; revert this; decide
-- `Std.DTreeMap.Internal.toList_roiIter` (idx 3, necessary): model CY: tree [0, 1], lowerBound 2
theorem t_roi_inst : ¬ (drop0% _private.Std.Data.DTreeMap.Internal.Zipper.«0».Std.DTreeMap.Internal.toList_roiIter 3) := fun H => by
  have := @H CY (fun _ => Nat) _ tCY tCY_ord 2
  rw [roiIterator, z_toList] at this; revert this; decide
-- `Std.DTreeMap.Internal.toList_roiIter` (idx 5, necessary): Nat: unordered tree [1, 0], lowerBound 0
theorem t_roi_ord : ¬ (drop0% _private.Std.Data.DTreeMap.Internal.Zipper.«0».Std.DTreeMap.Internal.toList_roiIter 5) := fun H => by
  have := @H Nat (fun _ => Nat) _ _ tUn 0
  rw [roiIterator, z_toList] at this; revert this; decide

end StdLeanHand

open Std Std.DTreeMap.Internal Std.Iterators

namespace StdLeanHand

/-! Remaining Lean rows. -/

-- `Lean.RArray.get_ofFn.go` (idx 9, necessary): n = 2, f = val, i = 1, lb = 0, ub = 1: go is leaf (f 0), get 1 = 0 != 1
theorem t_rarray9 : ¬ (drop0% _private.Lean.Data.RArray.«0».Lean.RArray.get_ofFn.go 9) := fun H => by
  have := H (n := 2) (fun i => i.val) 1 0 1 (by decide) (by decide) (by decide)
  rw [eqn% _private.Lean.Data.RArray.«0».Lean.RArray.ofFn.go 0] at this
  simp [Lean.RArray.get] at this

-- `Lean.Elab.Tactic.Do.ProofMode.assembled_proof` (idx 8, necessary): sigma = [], P = Q = H = True, H' = P' = T = False
theorem t_assembled8 : ¬ (drop0% _private.Lean.Elab.Tactic.Do.ProofMode.Cases.«0».Lean.Elab.Tactic.Do.ProofMode.assembled_proof 8) := fun H =>
  H (σs := []) (P := ⟨True⟩) (P' := ⟨False⟩) (Q := ⟨True⟩) (H := ⟨True⟩) (H' := ⟨False⟩) (T := ⟨False⟩)
    (by simp) (by simp) (by simp) trivial
-- `Lean.Elab.Tactic.Do.ProofMode.assembled_proof` (idx 9, necessary): sigma = [], P = Q = H = H' = True, P' = T = False
theorem t_assembled9 : ¬ (drop0% _private.Lean.Elab.Tactic.Do.ProofMode.Cases.«0».Lean.Elab.Tactic.Do.ProofMode.assembled_proof 9) := fun H =>
  H (σs := []) (P := ⟨True⟩) (P' := ⟨False⟩) (Q := ⟨True⟩) (H := ⟨True⟩) (H' := ⟨True⟩) (T := ⟨False⟩)
    (by simp) (by simp) (by simp) trivial
-- `Lean.Elab.Tactic.Do.ProofMode.assembled_proof` (idx 10, necessary): sigma = [], all True except T = False
theorem t_assembled10 : ¬ (drop0% _private.Lean.Elab.Tactic.Do.ProofMode.Cases.«0».Lean.Elab.Tactic.Do.ProofMode.assembled_proof 10) := fun H =>
  H (σs := []) (P := ⟨True⟩) (P' := ⟨True⟩) (Q := ⟨True⟩) (H := ⟨True⟩) (H' := ⟨True⟩) (T := ⟨False⟩)
    (by simp) (by simp) (by simp) trivial

/-! Hash map internals. -/

-- `Std.DHashMap.Internal.Raw₀.expand.go_pos` (idx 6, necessary): dependent; i = 0, source = #[]
theorem t_go_pos : ¬ (indep0% _private.Std.Data.DHashMap.Internal.WF.«0».Std.DHashMap.Internal.Raw₀.expand.go_pos 6) := fun H =>
  Nat.lt_irrefl 0 (@H Nat (fun _ => Nat) _ 0 #[] ⟨#[.nil], by decide⟩)

-- `Std.DHashMap.Internal.Raw₀.expand.go_neg` (idx 6, necessary): i = 0, source = #[[(0,0)]], target = #[[]]: go reinserts (0,0), toListModel length 1 != 0
theorem t_go_neg : ¬ (drop0% _private.Std.Data.DHashMap.Internal.WF.«0».Std.DHashMap.Internal.Raw₀.expand.go_neg 6) := fun H => by
  have h0 := @H Nat (fun _ => Nat) _ 0 #[.cons 0 0 .nil] ⟨#[.nil], by decide⟩
  rw [priv% _private.Std.Data.DHashMap.Internal.WF.«0».Std.DHashMap.Internal.Raw₀.expand.go_pos,
    priv% _private.Std.Data.DHashMap.Internal.WF.«0».Std.DHashMap.Internal.Raw₀.expand.go_neg] at h0
  · have := congrArg (fun t => (DHashMap.Internal.toListModel t.1).length) h0
    have hp := (DHashMap.Internal.Raw₀.toListModel_reinsertAux (β := fun _ => Nat) ⟨#[.nil], by decide⟩ 0 0).length_eq
    change (DHashMap.Internal.toListModel (DHashMap.Internal.Raw₀.reinsertAux (β := fun _ : Nat => Nat) hash
      ⟨#[.nil], by decide⟩ 0 0).1).length = (DHashMap.Internal.toListModel (β := fun _ : Nat => Nat) #[.nil]).length at this
    rw [hp] at this
    simp [DHashMap.Internal.toListModel] at this
  · simp
  · simp

-- `Std.ExtDHashMap.insertMany_list_mk` (idx 4, necessary): dependent; model NB (== always false, constant hash): EquivBEq fails (not reflexive)
theorem t_extIns : ¬ (indep0% _private.Std.Data.ExtDHashMap.Lemmas.«0».Std.ExtDHashMap.insertMany_list_mk 4) := fun H => by
  have h := @H NB _ _ (fun _ => Nat) _ ∅ []
  have := @ReflBEq.rfl NB _ h.toReflBEq 0
  simp [BEq.beq] at this

/-! Iterator models (from `checks/OpEHand.lean`). -/

theorem wf_irrefl {α : Sort u} {r : α → α → Prop} (h : WellFounded r) (a : α) : ¬ r a a := by
  have := h.apply a
  induction this with
  | intro x _ ih => exact fun hx => ih x hx hx

/-- `YL`: yields `0` and stays (productive, never skips). -/
structure YL where u : Unit
instance YL.inst {m : Type → Type} [Pure m] : Iterator YL m Nat where
  IsPlausibleStep it s := s = .yield it 0
  step it := pure (.deflate ⟨.yield it 0, rfl⟩)
instance YL.productive {m : Type → Type} [Pure m] : Productive YL m :=
  ⟨⟨fun a => ⟨a, fun b h => by cases h⟩⟩⟩
abbrev ylm : IterM (α := YL) Id Nat := ⟨⟨()⟩⟩

/-- `EM`: always done. -/
structure EM where u : Unit
instance EM.inst {m : Type → Type} [Pure m] : Iterator EM m Nat where
  IsPlausibleStep _ s := s = .done
  step _ := pure (.deflate ⟨.done, rfl⟩)
abbrev emm : IterM (α := EM) Id Nat := ⟨⟨()⟩⟩

/-- `LP`: skips to itself (not productive). -/
structure LP where u : Unit
instance LP.inst {m : Type → Type} [Pure m] : Iterator LP m Nat where
  IsPlausibleStep it s := s = .skip it
  step it := pure (.deflate ⟨.skip it, rfl⟩)
abbrev lpm : IterM (α := LP) Id Nat := ⟨⟨()⟩⟩
theorem LP.not_productive {m : Type → Type} [Pure m] : ¬ Productive LP m :=
  fun h => wf_irrefl h.wf ⟨⟨()⟩⟩ rfl

/-- `BM`: `Option` with `pure _ := none` (a monad that is not lawful). -/
def BM (α : Type) := Option α
instance : Monad BM where
  pure _ := (none : Option _)
  bind x f := Option.bind x f

theorem drop_rel_irrefl (x : IterM (α := Types.Drop YL Id Nat) Id Nat) :
    ¬ (priv% _private.Std.Data.Iterators.Combinators.Monadic.Drop.«0».Std.Iterators.Types.Drop.ProductiveRel) Id x x :=
  wf_irrefl (InvImage.wf _ (Prod.lex Nat.lt_wfRel IterM.TerminationMeasures.instWellFoundedRelationProductive).wf) x

-- `Std.Iterators.Types.Drop.productiveRel_of_inner` (idx 5, necessary): dependent; LP (skips to itself) is not productive
theorem t_dropInner_inst : ¬ (indep0% _private.Std.Data.Iterators.Combinators.Monadic.Drop.«0».Std.Iterators.Types.Drop.productiveRel_of_inner 5) :=
  fun H => LP.not_productive (@H LP Id Nat _ _ 0 lpm lpm)
-- `Std.Iterators.Types.Drop.productiveRel_of_inner` (idx 9, necessary): YL (productive), it = it': ProductiveRel is irreflexive (well-founded)
theorem t_dropInner_h : ¬ (drop0% _private.Std.Data.Iterators.Combinators.Monadic.Drop.«0».Std.Iterators.Types.Drop.productiveRel_of_inner 9) :=
  fun H => drop_rel_irrefl _ (@H YL Id Nat _ _ _ 0 ylm ylm)
-- `Std.Iterators.Types.Drop.productiveRel_of_remaining` (idx 5, necessary): dependent; LP (skips to itself) is not productive
theorem t_dropRem_inst : ¬ (indep0% _private.Std.Data.Iterators.Combinators.Monadic.Drop.«0».Std.Iterators.Types.Drop.productiveRel_of_remaining 5) :=
  fun H => LP.not_productive (@H LP Id Nat _ _ (lpm.drop 1) (lpm.drop 0) Nat.zero_lt_one)
-- `Std.Iterators.Types.Drop.productiveRel_of_remaining` (idx 8, necessary): YL (productive), it = it': ProductiveRel is irreflexive (well-founded)
theorem t_dropRem_h : ¬ (drop0% _private.Std.Data.Iterators.Combinators.Monadic.Drop.«0».Std.Iterators.Types.Drop.productiveRel_of_remaining 8) :=
  fun H => drop_rel_irrefl _ (@H YL Id Nat _ _ _ (ylm.drop 0) (ylm.drop 0))

-- `Std.IterM.Equiv.step_eq.aux` (idx 5, necessary): dependent; BM (Option with pure _ := none) is not lawful
theorem t_stepEq_inst : ¬ (indep0% _private.Std.Data.Iterators.Lemmas.Equivalence.StepCongr.«0».Std.IterM.Equiv.step_eq.aux 5) := fun H => by
  have h := @H Nat EM EM BM _ _ _ ⟨⟨()⟩⟩ ⟨⟨()⟩⟩
  have := @LawfulMonad.pure_bind BM _ h Nat Nat 0 (fun _ => (some 0 : Option Nat))
  have : (none : Option Nat) = some 0 := this
  cases this

-- `Std.IterM.Equiv.step_eq.aux` (idx 10, necessary): ita = EM (done), itb = YL (yields), s = done
theorem t_stepEq_h : ¬ (drop0% _private.Std.Data.Iterators.Lemmas.Equivalence.StepCongr.«0».Std.IterM.Equiv.step_eq.aux 10) := fun H => by
  obtain ⟨⟨s1, hs1⟩, hs⟩ := @H Nat EM YL Id _ _ _ _ emm ylm .done (HetT.property_map.2 ⟨.done, rfl, rfl⟩)
  change s1 = _ at hs1
  subst hs1
  cases hs

-- `Std.IterM.Equiv.step_eq.aux` (idx 12, necessary): ita = itb = EM (Equiv.refl), s = skip _: EM only plausibly steps to done
theorem t_stepEq_a : ¬ (drop0% _private.Std.Data.Iterators.Lemmas.Equivalence.StepCongr.«0».Std.IterM.Equiv.step_eq.aux 12) := fun H => by
  obtain ⟨⟨s1, hs1⟩, hs⟩ := @H Nat EM EM Id _ _ _ _ emm emm (IterM.Equiv.refl emm) (.skip (Quot.mk _ (BundledIterM.ofIterM emm)))
  change s1 = _ at hs1
  subst hs1
  cases hs

-- `Std.IterM.Equiv.step_eq.aux_subtypeMk_congr` (idx 6, necessary): alpha = Bool, P = False, Q = R = True: HEq forces the subsingleton function type Bool -> False -> _ to equal Bool -> True -> {x : Bool // True}
theorem t_subtypeMk : ¬ (drop0% _private.Std.Data.Iterators.Lemmas.Equivalence.StepCongr.«0».Std.IterM.Equiv.step_eq.aux_subtypeMk_congr 6) := fun H => by
  have hh := @H Bool (fun _ => False) (fun _ => True) (fun _ => True) (fun _ _ => trivial) (fun _ _ => trivial)
  have e := type_eq_of_heq hh
  have hs : ∀ x y : ((a : Bool) → False → {x : Bool // True}), x = y :=
    fun x y => funext fun a => funext fun h => h.elim
  let g1 : (a : Bool) → True → {x : Bool // True} := fun a _ => ⟨a, trivial⟩
  let g2 : (a : Bool) → True → {x : Bool // True} := fun _ _ => ⟨true, trivial⟩
  have h2 := congrArg (cast e) (hs (cast e.symm g1) (cast e.symm g2))
  simp only [cast_cast, cast_eq] at h2
  have := congrArg Subtype.val (congrFun (congrFun h2 false) trivial)
  simp [g1, g2] at this

/-! `Std.Do`, `Std.Http`, `Std.Internal`. -/

-- `Std.Do.WhileVariant.add_eval` (idx 6, necessary): ps = .pure, P = True, Q = False
theorem t_addEval : ¬ (drop0% _private.Std.Do.Triple.SpecLemmas.«0».Std.Do.WhileVariant.add_eval 6) := fun H =>
  @H Unit .pure ⟨True⟩ ⟨False⟩ (fun _ => ⟨0⟩) () trivial

-- `Std.Http.URI.autf8EncodeChar_flatMap_ascii` (idx 1, necessary): a = [200]: encoded as two bytes
theorem t_utf8 : ¬ (drop0% _private.Std.Http.Data.URI.Encoding.«0».Std.Http.URI.autf8EncodeChar_flatMap_ascii 1) := fun H => by
  have := @H [200]
  revert this; decide
-- `Std.Http.URI.isEncodedChar_isAscii` (idx 2, necessary): c = 200
theorem t_encChar : ¬ (drop0% _private.Std.Http.Data.URI.Encoding.«0».Std.Http.URI.isEncodedChar_isAscii 2) := fun H => by
  have := @H (fun _ => false) 200
  revert this; decide
-- `Std.Http.URI.isEncodedQueryChar_isAscii` (idx 2, necessary): c = 200
theorem t_encQChar : ¬ (drop0% _private.Std.Http.Data.URI.Encoding.«0».Std.Http.URI.isEncodedQueryChar_isAscii 2) := fun H => by
  have := @H (fun _ => false) 200
  revert this; decide
-- `Std.Http.URI.isHexDigit_isAscii` (idx 1, necessary): c = 200
theorem t_hexAscii : ¬ (drop0% _private.Std.Http.Data.URI.Encoding.«0».Std.Http.URI.isHexDigit_isAscii 1) := fun H => by
  have := @H 200
  revert this; decide

-- `Std.Internal.forIn'_cast` (idx 6, necessary): dependent; l = [], l' = [0]
theorem t_forIn : ¬ (indep0% _private.Std.Internal.ForIn.Lemmas.«0».Std.Internal.forIn'_cast 6) := fun H => by
  have := @H Nat Nat Id _ [] [0] 0 (fun _ _ d => pure (.done d))
  cases this

-- `Lean.Order.pprod_le` (idx 6, necessary): ImplicationOrder x ImplicationOrder, p = (True, True), q = (False, True)
theorem t_pprod1 : ¬ (drop0% _private.Std.Internal.Order.Product.«0».Lean.Order.pprod_le 6) := fun H =>
  (@H Lean.Order.ImplicationOrder _ Lean.Order.ImplicationOrder _ ⟨True, True⟩ ⟨False, True⟩ (fun h => h)).1 trivial
-- `Lean.Order.pprod_le` (idx 7, necessary): ImplicationOrder x ImplicationOrder, p = (True, True), q = (True, False)
theorem t_pprod2 : ¬ (drop0% _private.Std.Internal.Order.Product.«0».Lean.Order.pprod_le 7) := fun H =>
  (@H Lean.Order.ImplicationOrder _ Lean.Order.ImplicationOrder _ ⟨True, True⟩ ⟨True, False⟩ (fun h => h)).2 trivial

/-! Removable. -/

-- `Std.Time.Duration.ofNanoseconds.mod_nonpos` (idx 3, removable): tmod takes the sign of the dividend: (-a).tmod b = -(a.tmod b) >= 0 for any b (Int.neg_tmod, Int.tmod_nonneg)
theorem r_modNonpos : drop% _private.Std.Time.Duration.«0».Std.Time.Duration.ofNanoseconds.mod_nonpos 3 := by
  intro a b ha
  have := Int.tmod_nonneg b (Int.neg_nonneg_of_nonpos ha)
  rw [Int.neg_tmod] at this
  omega

-- `Std.Http.Internal.Char.not_quotedStringChar_ofNat_aux` (idx 1, removable): quotedStringChar c implies c < 0x80 (quotedStringChar_lt_0x80), so the c < 128 case applies to (Char.ofNat c).toNat
theorem r_quoted : drop% _private.Std.Http.Internal.Char.«0».Std.Http.Internal.Char.not_quotedStringChar_ofNat_aux 1 := by
  intro c h hq
  have hlt := Std.Http.Internal.Char.quotedStringChar_lt_0x80 hq
  rw [Char.lt_def] at hlt
  have := (priv% _private.Std.Http.Internal.Char.«0».Std.Http.Internal.Char.not_quotedStringChar_ofNat_aux)
    (Char.ofNat c).toNat hlt
  rw [Char.ofNat_toNat] at this
  exact this h hq

-- `Std.DTreeMap.Internal.Zipper.prependMap_pruneLE_eq_prependMapGE` (idx 4, removable): both sides follow the same compare branches node by node; induction on t without ordering
theorem r_pruneLE_GE : drop% _private.Std.Data.DTreeMap.Internal.Zipper.«0».Std.DTreeMap.Internal.Zipper.prependMap_pruneLE_eq_prependMapGE 4 := by
  intro α β _ t z lb
  induction t generalizing z with
  | leaf => rfl
  | inner sz k v l r ihl ihr =>
    rw [eqn% _private.Std.Data.DTreeMap.Internal.Zipper.«0».Std.DTreeMap.Internal.Impl.pruneLE 1]
    cases hc : compare lb k <;> simp only [hc, Zipper.prependMap, Zipper.prependMapGE]
    · exact ihl _
    · exact ihr _

-- `Std.DTreeMap.Internal.Zipper.prependMap_eq_prependMapGT_self` (idx 7, removable): hyp alone forces the lt branch at every node of the left spine; induction on r without ordering
theorem r_GT_self : drop% _private.Std.Data.DTreeMap.Internal.Zipper.«0».Std.DTreeMap.Internal.Zipper.prependMap_eq_prependMapGT_self 7 := by
  intro α β _ _ r
  induction r with
  | leaf => intro z lb _; rfl
  | inner sz k v l r ihl _ =>
    intro z lb hyp
    have hk : compare lb k = .lt := hyp ⟨k, v⟩ (by simp [Impl.toList_eq_toListModel])
    simp only [Zipper.prependMap, Zipper.prependMapGT, hk]
    exact ihl _ lb (fun e he => hyp e (by simp_all [Impl.toList_eq_toListModel]))

end StdLeanHand

