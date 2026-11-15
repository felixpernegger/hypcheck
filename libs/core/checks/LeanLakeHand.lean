import Lean
import Lake

/-!
Hand resolution of the 39 hypotheses in `Lean.*` and `Lake.*` that `HypCheck.lean` left unresolved.
For each hypothesis `hᵢ` of theorem `T`, this file proves `T'` (removable) or `¬T'` (necessary); for
dependent hypotheses necessity means `¬ ∀ indep, Hᵢ` (see `Methods.md`). Universe-polymorphic
theorems are refuted at universe 0. Three hypotheses are left open (see the end of the file).

Run with the lean4 repo's stage1 binary: `lean checks/LeanLakeHand.lean`.
-/

open Lean Lake

namespace LeanLakeHand

/-- A type cannot equal every type. Refutes the `FamilyDef`/`FamilyOut` instances below, whose
conclusion `F x = α` is claimed for all `α`. -/
theorem not_eq_all {T : Type} : ¬ ∀ α : Type, T = α := fun h =>
  (cast ((h Unit).symm.trans (h Empty)) ()).elim

/-- `n` with a macro scope. -/
def withScope : Name := Lean.addMacroScope `Foo `x 1

theorem isPrefixOf_str {p q : Name} (s : String) (h : p.isPrefixOf q) :
    p.isPrefixOf (.str q s) := by
  simp [Name.isPrefixOf, h]

theorem isPrefixOf_num {p q : Name} (k : Nat) (h : p.isPrefixOf q) :
    p.isPrefixOf (.num q k) := by
  simp [Name.isPrefixOf, h]

theorem isPrefixOf_appendCore {p q : Name} (h : p.isPrefixOf q) :
    ∀ r, p.isPrefixOf (Name.appendCore q r)
  | .anonymous => by simpa [Name.appendCore] using h
  | .str r s => by simpa [Name.appendCore] using isPrefixOf_str s (isPrefixOf_appendCore h r)
  | .num r k => by simpa [Name.appendCore] using isPrefixOf_num k (isPrefixOf_appendCore h r)

theorem isPrefixOf_foldl_mkNum {p q : Name} (h : p.isPrefixOf q) :
    ∀ (ks : List Nat), p.isPrefixOf (ks.foldl Name.mkNum q)
  | [] => h
  | k :: ks => isPrefixOf_foldl_mkNum (isPrefixOf_num k h) ks

end LeanLakeHand

open LeanLakeHand

/-! # Removable (1) -/

-- `Lake.Name.isPrefixOf_append` (`¬m.hasMacroScopes`): if only `m` has macro scopes, `n ++ m`
-- is `n.appendCore m.eraseMacroScopes` followed by the macro scope suffix, so it still starts with `n`.
theorem LeanLakeHand.Name.isPrefixOf_append {n m : Name} (h1 : ¬ n.hasMacroScopes) :
    n.isPrefixOf (n ++ m) := by
  by_cases h2 : m.hasMacroScopes
  · change n.isPrefixOf (n.append m)
    have h1' : n.hasMacroScopes = false := by simpa using h1
    simp only [Name.append, h1', h2, MacroScopesView.review]
    have base := isPrefixOf_appendCore (Lake.Name.isPrefixOf_self (n := n))
      (extractMacroScopes m).name
    split
    · exact base
    · apply isPrefixOf_foldl_mkNum
      apply isPrefixOf_str
      apply isPrefixOf_appendCore
      apply isPrefixOf_appendCore
      exact isPrefixOf_str _ base
  · exact Lake.Name.isPrefixOf_append h1 h2

example : type_of% @Lake.Name.isPrefixOf_append := fun h1 _ => LeanLakeHand.Name.isPrefixOf_append h1

/-! # Necessary (35) -/

/-! ## Lean -/

-- `Lean.Language.instNonemptySnapshotTask` (`[Nonempty α]`): a `SnapshotTask Empty` contains a
-- `Task Empty`, hence an element of `Empty`.
example : ¬ ∀ {α : Type}, Nonempty (Lean.Language.SnapshotTask α) := fun h =>
  (h (α := Empty)).elim fun s => s.task.get.elim

-- `Lean.Parser.InputContext.not_atEnd_inputString` (`¬c.atEnd p`): the empty input at position 0.
example : ¬ ∀ {c : Lean.Parser.InputContext} {p : String.Pos.Raw},
    ¬ String.Pos.Raw.atEnd c.inputString p = true := fun h =>
  @h default 0 (by decide)

-- `Lean.Meta.Rfl.rel_of_eq_and_refl` (`hxy : x = y`): `R := Eq` on `Bool`, `x := true`, `y := false`.
example : ¬ ∀ {α : Sort 1} {R : α → α → Prop} {x y : α}, R x x → R x y := fun h =>
  absurd (@h Bool Eq true false rfl) (by decide)

-- `Lean.Meta.Rfl.rel_of_eq_and_refl` (`h : R x x`): `R := False`.
example : ¬ ∀ {α : Sort 1} {R : α → α → Prop} {x y : α}, x = y → R x y := fun h =>
  @h Unit (fun _ _ => False) () () rfl

-- `Lean.Elab.Tactic.Omega.List.nonzeroMinimum_map_le_nonzeroMinimum` (`h`): `p := 0`, `q := 5`.
example : ¬ ∀ {α : Type} {β : Type} (f : α → β) (p : α → Nat) (q : β → Nat) (xs : List α),
    (∀ a, a ∈ xs → p a ≠ 0 → q (f a) ≤ p a) →
      Lean.Elab.Tactic.Omega.List.nonzeroMinimum (List.map q (List.map f xs)) ≤
        Lean.Elab.Tactic.Omega.List.nonzeroMinimum (List.map p xs) := fun h =>
  absurd (h (α := Nat) (β := Nat) id (fun _ => 0) (fun _ => 5) [0] (by simp)) (by decide)

-- `Lean.Elab.Tactic.Omega.List.nonzeroMinimum_map_le_nonzeroMinimum` (`w`): `p := 1`, `q := 2`.
example : ¬ ∀ {α : Type} {β : Type} (f : α → β) (p : α → Nat) (q : β → Nat) (xs : List α),
    (∀ a, a ∈ xs → (p a = 0 ↔ q (f a) = 0)) →
      Lean.Elab.Tactic.Omega.List.nonzeroMinimum (List.map q (List.map f xs)) ≤
        Lean.Elab.Tactic.Omega.List.nonzeroMinimum (List.map p xs) := fun h =>
  absurd (h (α := Nat) (β := Nat) id (fun _ => 1) (fun _ => 2) [0] (by simp)) (by decide)

-- `Lean.RArray.get_ofFn`, `Lean.RArray.size_ofFn` (`h : 0 < n`, dependent): independent
-- parameters `α`, `n`, `f`; `n := 0`.
example : ¬ ∀ {α : Type} {n : Nat} (_f : Fin n → α), 0 < n := fun h =>
  absurd (@h Unit 0 Fin.elim0) (by decide)

/-! ## Lake: names and keys -/

-- `Lake.Name.eq_anonymous_of_isAnonymous` (`h`)
example : ¬ ∀ {n : Name}, n = .anonymous := fun h => absurd (@h `a) (by decide)

-- `Lake.Name.eq_of_quickCmp` (`a`)
example : ¬ ∀ {n n' : Name}, n = n' := fun h => absurd (@h `a `b) (by decide)

-- `Lake.BuildKey.eq_of_quickCmp` (`a`)
example : ¬ ∀ {k k' : BuildKey}, k = k' := fun h => absurd (@h (.module `a) (.module `b)) (by decide)

-- `Lake.Name.isPrefixOf_append` (`¬n.hasMacroScopes`): `n := x._@.Foo._hyg.1`, `m := y`; then
-- `n ++ m = x.y._@.Foo._hyg.1`.
example : ¬ ∀ {n m : Name}, ¬ m.hasMacroScopes = true → n.isPrefixOf (n ++ m) = true := fun h =>
  absurd (@h withScope `y (by decide)) (by decide)

/-! ## Lake: families -/

-- `Lake.FamilyOut.fam_eq`, `Lake.FamilyDef.fam_eq` (`self`)
example : ¬ ∀ {α β : Type} {f : α → β} {a : α} {b : β}, f a = b := fun h =>
  absurd (@h Nat Nat id 0 1) (by decide)

-- `Lake.instFamilyOutOfFamilyDef` (`[FamilyDef f a b]`)
example : ¬ ∀ {α β : Type} {f : α → β} {a : α} {b : β}, FamilyOut f a b := fun h =>
  absurd (@h Nat Nat id 0 1).fam_eq (by decide)

-- The `FamilyDef` instances of `Lake.Build.Data` and `Lake.Build.Info`: without their premise the
-- conclusion `F x = α` holds for every `α`.

-- `Lake.instFamilyDefBuildKeyBuildDataModuleOfFamilyOutNameDataTypeFacetKind` (`inst`)
example : ¬ ∀ {α : Type} {k : Name}, FamilyDef BuildData (BuildKey.module k) α := fun h =>
  not_eq_all fun α => (@h α `a).fam_eq

-- `Lake.instFamilyDefBuildKeyBuildDataPackageModuleOfFamilyOutNameDataTypeFacetKind` (`inst`)
example : ¬ ∀ {α : Type} {p m : Name}, FamilyDef BuildData (BuildKey.packageModule p m) α :=
  fun h => not_eq_all fun α => (@h α `a `b).fam_eq

-- `Lake.instFamilyDefBuildKeyBuildDataPackageOfFamilyOutNameDataTypeFacetKind` (`inst`)
example : ¬ ∀ {α : Type} {k : Name}, FamilyDef BuildData (BuildKey.package k) α := fun h =>
  not_eq_all fun α => (@h α `a).fam_eq

-- `Lake.instFamilyDefBuildKeyBuildDataPackageTargetOfFamilyOutNameCustomData` (`inst`)
example : ¬ ∀ {p t : Name} {α : Type}, FamilyDef BuildData (BuildKey.packageTarget p t) α :=
  fun h => not_eq_all fun α => (@h `a `b α).fam_eq

-- `Lake.instFamilyDefNameCustomDataOfProdCustomOutMk` (`h`)
example : ¬ ∀ {p t : Name} {α : Type}, FamilyDef (CustomData p) t α := fun h =>
  not_eq_all fun α => (@h `a `b α).fam_eq

-- `Lake.instFamilyDefNameFacetDataOfFacetOutHAppend` (`h`)
example : ¬ ∀ {kind facet : Name} {α : Type}, FamilyDef (FacetData kind) facet α := fun h =>
  not_eq_all fun α => (@h `a `b α).fam_eq

-- `Lake.instFamilyDefNameFacetOutHAppendOfFacetData` (`h`)
example : ¬ ∀ {kind facet : Name} {α : Type}, FamilyDef FacetOut (kind ++ facet) α := fun h =>
  not_eq_all fun α => (@h `a `b α).fam_eq

-- `Lake.instFamilyDefBuildKeyBuildDataKeyTargetOfFamilyOutPackageTarget` and
-- `Lake.instFamilyDefBuildKeyBuildDataKeyTargetOfFamilyOutNameCustomData` (`inst`): same
-- statement without the premise; `p` is any package.
example : ¬ ∀ {n t : Name} {α : Type} {p : NPackage n},
    FamilyDef BuildData (BuildInfo.target p.toPackage t).key α := fun h =>
  let pkg : Package := Classical.ofNonempty
  not_eq_all fun α => (@h pkg.keyName `t α ⟨pkg, rfl⟩).fam_eq

-- `Lake.instFamilyDefBuildKeyBuildDataKeyFacetOfFamilyOutNameFacetOut` (`inst`)
example : ¬ ∀ {f : Name} {α : Type} {t : BuildKey} {k : Name} {d : DataType k},
    FamilyDef BuildData (BuildInfo.facet t k d f).key α := fun h =>
  not_eq_all fun α =>
    (@h `f α (.module `a) `unit
      (cast (FamilyDef.fam_eq (f := DataType.{0}) (a := `unit) (b := Unit)).symm ())).fam_eq

-- `Lake.OptDataKind.wf` (`h`): an `OptDataKind` with anonymous name says nothing about `α`.
example : ¬ ∀ {α : Type} [_self : OptDataKind α], α = DataType.{0} (OptDataKind.name α) := fun h =>
  not_eq_all (T := DataType.{0} .anonymous) fun α =>
    (@h α ⟨.anonymous, fun h => absurd rfl h⟩).symm

-- `Lake.OptDataKind.eq_data_type` (`h`)
example : ¬ ∀ {α : Type} {_self : OptDataKind α}, α = DataType.{0} (OptDataKind.name α) := fun h =>
  not_eq_all (T := DataType.{0} .anonymous) fun α =>
    (@h α ⟨.anonymous, fun h => absurd rfl h⟩).symm

/-! ## Lake: workspaces -/

namespace LeanLakeHand

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

/-- A well-formed workspace. -/
noncomputable def ws1 : Workspace := ⟨raw1, raw1_wf⟩

end LeanLakeHand

-- `Lake.Workspace.Raw.WF.size_packages_pos` (`self`): no packages.
example : ¬ ∀ {ws : Workspace.Raw}, 0 < ws.packages.size := fun h =>
  absurd (@h { (Classical.ofNonempty : Workspace.Raw) with packages := #[] }) (by simp)

-- `Lake.Workspace.Raw.WF.packages_wsIdx` (`self`): one package with index 1.
example : ¬ ∀ {ws : Workspace.Raw} {i : Nat} (h : i < ws.packages.size), ws.packages[i].wsIdx = i :=
  fun h => absurd (@h { (Classical.ofNonempty : Workspace.Raw) with packages := #[pkg 1 #[]] } 0
    (by simp)) (by simp [pkg])

-- `Lake.Workspace.Raw.WF.packages_wsIdx` (`h : i < ws.packages.size`, dependent): independent
-- parameters `ws`, `self`, `i`; `i := ws.packages.size`.
example : ¬ ∀ {ws : Workspace.Raw}, ws.WF → ∀ {i : Nat}, i < ws.packages.size := fun h =>
  Nat.lt_irrefl _ (@h raw1 raw1_wf raw1.packages.size)

-- `Lake.Workspace.Raw.WF.depIdxs_packages` (`self`): a package depending on index 5.
example : ¬ ∀ {ws : Workspace.Raw} (pkg : Package), pkg ∈ ws.packages →
    ∀ (i : Nat), i ∈ pkg.depIdxs → i < ws.packages.size := fun h =>
  absurd (@h { (Classical.ofNonempty : Workspace.Raw) with packages := #[pkg 0 #[5]] } (pkg 0 #[5])
    (by simp) 5 (by simp [pkg])) (by simp)

-- `Lake.Workspace.Raw.WF.depIdxs_packages` (`pkg ∈ ws.packages`): a package outside the workspace.
example : ¬ ∀ {ws : Workspace.Raw}, ws.WF → ∀ (pkg : Package) (i : Nat), i ∈ pkg.depIdxs →
    i < ws.packages.size := fun h =>
  Nat.lt_irrefl _ (@h raw1 raw1_wf (pkg 0 #[raw1.packages.size]) _ (by simp [pkg]))

-- `Lake.Workspace.Raw.WF.depIdxs_packages` (`i ∈ pkg.depIdxs`): `i := ws.packages.size`.
example : ¬ ∀ {ws : Workspace.Raw}, ws.WF → ∀ (pkg : Package), pkg ∈ ws.packages →
    ∀ (i : Nat), i < ws.packages.size := fun h =>
  Nat.lt_irrefl _ (@h raw1 raw1_wf (raw1.packages[0]'raw1_wf.size_packages_pos)
    (Array.getElem_mem _) raw1.packages.size)

-- `Lake.Workspace.packages_addPackage'` (`h : pkg.wsIdx = ws.packages.size`, dependent):
-- independent parameters `pkg`, `ws`.
example : ¬ ∀ {pkg : Package} {ws : Workspace}, pkg.wsIdx = ws.packages.size := fun h =>
  absurd (@h (pkg (ws1.packages.size + 1) #[]) ws1) (by simp [pkg])

-- `Lake.Workspace.packages_addPackage'` (`h' : pkg.depIdxs = #[]`, dependent)
example : ¬ ∀ {pkg : Package}, pkg.depIdxs = #[] := fun h =>
  absurd (@h (pkg 0 #[0])) (by simp [pkg])

/-! # Left open (3): independent of the axioms

`Lake.ConfigDecl.wf_data` (`a : ¬self.kind.isAnonymous`), `Lake.NConfigDecl.target_eq_type` and
`Lake.NConfigDecl.data_eq_target` (`h : ¬self.kind.isAnonymous`). Declarations with an anonymous
kind exist (`ConfigType .anonymous p n = OpaqueTargetConfig p n` is a `nonempty_type`). For them the
statements without the hypothesis say `CustomOut (p, n) = DataType .anonymous` (for all `p`, `n`)
and `DataType .anonymous = OpaqueConfigTarget .anonymous`. `CustomOut`, `DataType` and
`OpaqueConfigTarget` are `opaque` families; the only axioms about them fix other indices
(`family_def`, `OpaqueConfigTarget.def`). So these equations can neither be proved nor refuted,
and the hypotheses are neither provably removable nor provably necessary.
-/
