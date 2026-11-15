import Lean.Elab.Command
import Iris
-- hypkit toolkit header: drop%/indep%/drop0%/indep0% state T' and ∀ indep, Hᵢ straight from the library.
-- Agents copy this file unchanged as the start of their output file (scripts/verify.sh checks it).
-- No `xs[i]!` here: libraries may declare a `]!` token (Foundation does), which breaks that syntax.


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
    let x := (xs.getD (i.getNat) default)
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType (xs.getD (j) default)).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

/-- `indep% T i`: `∀ indep, Hᵢ` for the dependent Prop binder `i` of `T` (all independent binders). -/
elab "indep% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := (xs.getD (i.getNat) default)
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    let mut dep := #[x]
    for j in [i.getNat+1:xs.size] do
      let t ← inferType (xs.getD (j) default)
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push (xs.getD (j) default)
    unless or (decide (dep.size > 1)) (body.containsFVar x.fvarId!) do
      throwError "binder {i.getNat} of {n} is not dependent"
    mkForallFVars (xs.filter (fun y => !dep.contains y)) (← inferType x)

/-- `drop0% T i`: `drop% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "drop0% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.zero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := (xs.getD (i.getNat) default)
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType (xs.getD (j) default)).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

/-- `indep0% T i`: `indep% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "indep0% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.zero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := (xs.getD (i.getNat) default)
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    let mut dep := #[x]
    for j in [i.getNat+1:xs.size] do
      let t ← inferType (xs.getD (j) default)
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push (xs.getD (j) default)
    unless or (decide (dep.size > 1)) (body.containsFVar x.fvarId!) do
      throwError "binder {i.getNat} of {n} is not dependent"
    mkForallFVars (xs.filter (fun y => !dep.contains y)) (← inferType x)

/-- `priv% c`: the constant `c` (public, or private written as `_private.Mod.«0».x`), with fresh
universe levels; use it to mention private definitions and lemmas inside statements and proofs. -/
elab "priv% " c:ident : term => do
  mkConstWithFreshMVarLevels (← hcConst c)

namespace W7c0
open Iris Iris.BI

/-- Two-element commutative monoid (e unit, a idempotent) with the equality order: a non-affine UORA (Probe3). -/
inductive NA | e | a deriving DecidableEq

def NA.op : NA → NA → NA
  | .e, y => y
  | .a, _ => .a

instance : OFE NA := OFE.ofDiscrete NA
instance : OFE.Discrete NA := ⟨id⟩

instance instORA : ORA NA := ORA.ofDiscreteORAData {
  pcore := fun _ => some .e
  op := NA.op
  Valid := fun _ => True
  Order := Eq
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
  pcore_op_left := by intro x cx h; cases h; cases x <;> rfl
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := fun _ _ _ => trivial
  ord_trans := fun _ _ _ h1 h2 => h1.trans h2
  op_mono_left := by intro x y z h; cases h; rfl
  valid_of_ord := fun _ _ _ _ => trivial
  pcore_mono := by intro x y cx h1 h2; exact ⟨.e, rfl, by cases h2; rfl⟩
  pcore_order_op := by intro x cx h y; exact ⟨.e, rfl, by cases h; rfl⟩
  pcore_increasing := by intro x cx h y; cases h; rfl
  increasing_closed := by intro x y _ h; cases h; assumption }

instance : OrderRefl NA := ⟨fun x => show x = x from rfl⟩

instance instUORA : UORA NA where
  unit := .e
  unit_valid := trivial
  unit_left_id := rfl
  pcore_unit := rfl

/-- Two-element monoid (e unit, a absorbing) with the extension order: an affine UORA (Probe3). -/
inductive AF | e | a deriving DecidableEq

def AF.op : AF → AF → AF
  | .e, y => y
  | .a, _ => .a

instance : OFE AF := OFE.ofDiscrete AF
instance : OFE.Discrete AF := ⟨id⟩

instance instORAAF : ORA AF := ORA.ofDiscreteORAData {
  pcore := fun _ => some .e
  op := AF.op
  Valid := fun _ => True
  Order := fun x y => x = .e ∨ x = y
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
  pcore_op_left := by intro x cx h; cases h; cases x <;> rfl
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := fun _ _ _ => trivial
  ord_trans := by intro x y z h1 h2; cases x <;> cases y <;> cases z <;> simp_all
  op_mono_left := by intro x y z h; cases x <;> cases y <;> cases z <;> simp_all [AF.op]
  valid_of_ord := fun _ _ _ _ => trivial
  pcore_mono := by intro x y cx h1 h2; exact ⟨.e, rfl, by cases h2; exact .inl rfl⟩
  pcore_order_op := by intro x cx h y; exact ⟨.e, rfl, by cases h; exact .inl rfl⟩
  pcore_increasing := by intro x cx h y; cases h; exact .inr rfl
  increasing_closed := by intro x y hx h z; cases x <;> cases y <;> cases z <;> simp_all [AF.op] }

instance : OrderRefl AF := ⟨fun x => show x = .e ∨ x = x from .inr rfl⟩

instance instUORAAF : UORA AF where
  unit := .e
  unit_valid := trivial
  unit_left_id := rfl
  pcore_unit := rfl

instance : IncOrd AF := ⟨by
  intro x y ⟨z, hz⟩
  show x = .e ∨ x = y
  cases x <;> cases z <;> simp_all [Op.op, AF.op]⟩

/-- One-point-ish ORA valid only at step 0 (W4c3 `VZ`). -/
structure VZ where b : Bool
instance : OFE VZ := OFE.ofDiscrete VZ
instance : OFE.Discrete VZ := ⟨fun h => h⟩
instance vzOp : Op VZ where
  op _ _ := ⟨false⟩
  op_ne := ⟨fun _ _ _ _ => OFE.Dist.rfl⟩
  assoc := rfl
  comm := rfl
instance vzPCore : PCore VZ where
  pcore _ := none
  pcore_ne _ h := nomatch h
  pcore_idem h := nomatch h
instance vzValid : Iris.Valid VZ where
  ValidN n _ := n = 0
  Valid _ := False
  validN_ne _ h := h
  valid_iff_validN := ⟨False.elim, fun h => by have := h 1; omega⟩
  validN_succ h := by omega
instance vzOrdered : Ordered VZ where
  OrderN _ _ _ := True
  Order _ _ := True
  ordN_ne _ _ _ := trivial
  ordN_succ _ := trivial
  ordN_trans _ _ := trivial
  ord_trans _ _ := trivial
  ordN_of_ord _ _ := trivial
instance vzORA : ORA VZ where
  validN_op_left h := h
  pcore_op_left h := nomatch h
  extend {_ _ y₁ y₂} _ e := ⟨y₁, y₂, e, OFE.Dist.rfl, OFE.Dist.rfl⟩
  op_monoN_left_ord _ _ := trivial
  op_mono_left_ord _ _ := trivial
  validN_of_ordN _ h := h
  pcore_monoN_ord _ h := nomatch h
  pcore_mono_ord _ h := nomatch h
  pcore_order_op h := nomatch h
  pcore_increasing h := nomatch h
  increasing_closed _ _ := ⟨fun _ => trivial⟩
  ordN_extend {_ x _} _ _ := ⟨x, trivial, OFE.Dist.rfl⟩

/-- TD (W1c5): Nat with n-distance `min x n = min y n`, max, order ≤: a non-discrete UORA. -/
structure TD where v : Nat
instance tdOFE : OFE TD where
  Dist n x y := min x.v n = min y.v n
  dist_eqv := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩
  eq_dist' {x y} := ⟨fun h n => h ▸ rfl, fun h => by
      cases x with | mk a => cases y with | mk b =>
      have h' : min a (a+b+1) = min b (a+b+1) := h (a+b+1)
      simp only [TD.mk.injEq]; omega⟩
  dist_lt {n x y m} h hm := by
    have h' : min x.v n = min y.v n := h
    show min x.v m = min y.v m; omega
theorem td_dist {n} {x y : TD} : x ≡{n}≡ y ↔ min x.v n = min y.v n := Iff.rfl
/-- Max on TD with core 0, order ≤ (n-order on truncations): a UORA whose unit 0 is not discrete. -/
instance tdOp : Op TD where
  op x y := ⟨max x.v y.v⟩
  op_ne := ⟨fun n y z h => by
    show min (max _ y.v) n = min (max _ z.v) n
    have h' : min y.v n = min z.v n := h
    omega⟩
  assoc := by simp only [TD.mk.injEq]; omega
  comm := by simp only [TD.mk.injEq]; omega
instance tdPCore : PCore TD where
  pcore _ := some ⟨0⟩
  pcore_ne _ h := by cases h; exact ⟨_, rfl, OFE.Dist.rfl⟩
  pcore_idem h := by cases h; rfl
instance tdValid : Iris.Valid TD where
  ValidN _ _ := True
  Valid _ := True
  validN_ne _ h := h
  valid_iff_validN := ⟨fun _ _ => trivial, fun _ => trivial⟩
  validN_succ h := h
instance tdOrdered : Ordered TD where
  OrderN n x y := min x.v n ≤ min y.v n
  Order x y := x.v ≤ y.v
  ordN_ne {n x x' y y'} (hx : min x.v n = min x'.v n) (hy : min y.v n = min y'.v n) h := by
    show min x'.v n ≤ min y'.v n; omega
  ordN_succ {n x y} (h : min x.v (n+1) ≤ min y.v (n+1)) := show min x.v n ≤ min y.v n by omega
  ordN_trans {n x y z} (h1 : min x.v n ≤ min y.v n) (h2 : min y.v n ≤ min z.v n) :=
    show min x.v n ≤ min z.v n by omega
  ord_trans {x y z} (h1 : x.v ≤ y.v) (h2 : y.v ≤ z.v) := show x.v ≤ z.v by omega
  ordN_of_ord {x y} n (h : x.v ≤ y.v) := show min x.v n ≤ min y.v n by omega
def tdz (n : Nat) (x y : TD) : TD := if y.v < n then y else x
instance tdORA : ORA TD where
  validN_op_left _ := trivial
  pcore_op_left {x cx} h := by cases h; show (⟨max 0 x.v⟩ : TD) = x; cases x; simp
  extend {n x y₁ y₂} _ e := ⟨tdz n x y₁, tdz n x y₂, by
      have e' : min x.v n = min (max y₁.v y₂.v) n := e
      cases x with | mk a => cases y₁ with | mk b => cases y₂ with | mk c =>
      show TD.mk a = TD.mk (max (tdz n ⟨a⟩ ⟨b⟩).v (tdz n ⟨a⟩ ⟨c⟩).v)
      simp only at e'
      simp only [tdz, TD.mk.injEq]
      split <;> split <;> simp only <;> omega,
    by
      have e' : min x.v n = min (max y₁.v y₂.v) n := e
      show min (tdz n x y₁).v n = min y₁.v n
      simp only [tdz]; split <;> omega,
    by
      have e' : min x.v n = min (max y₁.v y₂.v) n := e
      show min (tdz n x y₂).v n = min y₂.v n
      simp only [tdz]; split <;> omega⟩
  op_monoN_left_ord {n x y} z (h : min x.v n ≤ min y.v n) :=
    show min (max x.v z.v) n ≤ min (max y.v z.v) n by omega
  op_mono_left_ord {x y} z (h : x.v ≤ y.v) := show max x.v z.v ≤ max y.v z.v by omega
  validN_of_ordN _ _ := trivial
  pcore_monoN_ord _ h := by cases h; exact ⟨_, rfl, show min 0 _ ≤ min 0 _ from Nat.le_refl _⟩
  pcore_mono_ord _ h := by cases h; exact ⟨_, rfl, show 0 ≤ 0 from Nat.le_refl _⟩
  pcore_order_op h _ := by cases h; exact ⟨_, rfl, show 0 ≤ 0 from Nat.le_refl _⟩
  pcore_increasing h := by cases h; exact ⟨fun y => show y.v ≤ max 0 y.v by omega⟩
  increasing_closed {_ _ y} _ _ := ⟨fun z => show z.v ≤ max y.v z.v by omega⟩
  ordN_extend {n x y} _ (h : min x.v n ≤ min y.v n) :=
    ⟨⟨min x.v n⟩, show min (min x.v n) (n+1) ≤ min y.v (n+1) by omega,
      show min (min x.v n) n = min x.v n by omega⟩
instance tdUORA : UORA TD where
  unit := ⟨0⟩
  unit_valid := trivial
  unit_left_id {x} := by show (⟨max 0 x.v⟩ : TD) = x; cases x; simp
  pcore_unit := rfl
  ord_refl x := show x.v ≤ x.v from Nat.le_refl _


/-! TX (W1c0): 3-element UORA with invalid z -/
inductive TX | e | a | z deriving DecidableEq
def TX.op : TX → TX → TX
  | .e, y => y
  | x, .e => x
  | .a, .a => .a
  | _, _ => .z
instance : OFE TX := OFE.ofDiscrete TX
instance : OFE.Discrete TX := ⟨id⟩
@[instance_reducible] def txData : DiscreteORAData TX where
  pcore := fun _ => some .e
  op := TX.op
  Valid := fun x => x ≠ .z
  Order := fun x y => y = .z ∨ x ≠ .z
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
  pcore_op_left := by intro x cx h; cases h; cases x <;> rfl
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := by intro x y; cases x <;> cases y <;> decide
  ord_trans := by intro x y z; cases x <;> cases y <;> cases z <;> decide
  op_mono_left := by intro x y z; cases x <;> cases y <;> cases z <;> decide
  valid_of_ord := by intro x y; cases x <;> cases y <;> decide
  pcore_mono := by intro x y cx h1 h2; cases h2; exact ⟨.e, rfl, by decide⟩
  pcore_order_op := by intro x cx h y; cases h; exact ⟨.e, rfl, by decide⟩
  pcore_increasing := by intro x cx h y; cases h; cases y <;> decide
  increasing_closed := by intro x y _ _ w; cases y <;> cases w <;> decide
instance txORA : ORA TX := ORA.ofDiscreteORAData txData
instance : ORA.Discrete TX := ORA.ofDiscreteORAData_discrete txData
instance : OrderRefl TX := ⟨fun x => show x = .z ∨ x ≠ .z by cases x <;> decide⟩
instance txUORA : UORA TX where
  unit := .e
  unit_valid := show TX.e ≠ .z by decide
  unit_left_id := rfl
  pcore_unit := rfl

end W7c0
open Iris Iris.BI W7c0


namespace W7c0
open Iris Iris.BI COFE Auth

/-- Closed-proofs GF (invariant, mask, credit slots 0–3) with the functor `F` in every slot ≥ 4. -/
noncomputable def GX (F : OFunctorPre) [RFunctorContractive F] [RFunctorAffine F] : BundledGFunctors := fun n =>
  match n with
  | 0  => ⟨InvMapF⟩
  | 1  => ⟨constOF CoPsetDisjL⟩
  | 2  => ⟨constOF (DisjointLeibnizSet PosSet)⟩
  | 3  => ⟨AuthURF (constOF Credit)⟩
  | _  => ⟨F⟩

section
variable (F : OFunctorPre) [RFunctorContractive F] [RFunctorAffine F]
instance gxWsat : WsatGpreS (GX F) where
  inv := { τ := 0, transp := by unfold GX; rfl }
  enabled := { τ := 1, transp := by unfold GX; rfl }
  disabled := { τ := 2, transp := by unfold GX; rfl }
instance gxLc : LcGpreS (GX F) where
  lc_elem := { τ := 3, transp := by unfold GX; rfl }
instance gxInv : InvGpreS (GX F) where
  toWsatGpreS := inferInstance
  toLcGpreS := inferInstance
/-- Slot 4 holds `F`. -/
instance gxElem : ElemG (GX F) F := { τ := 4, transp := by unfold GX; rfl }
/-- Slot 1 (disjoint masks) as a user resource: `valid ⊤` is exclusive. -/
@[instance_reducible] def gxElem1 : ElemG (GX F) (constOF CoPsetDisjL) := { τ := 1, transp := by unfold GX; rfl }
end

theorem full_not_disj : ¬ (CoPset.full ## CoPset.full) := fun hd => hd .xH ⟨rfl, rfl⟩

set_option linter.deprecated false in
/-- Owning `valid ⊤` twice at the same name (slot 1) is contradictory. -/
theorem own_full_dup_false {F : OFunctorPre} [RFunctorContractive F] [RFunctorAffine F] (γ : GName) :
    iOwn (E := gxElem1 F) γ (.valid CoPset.full) ∗ iOwn (E := gxElem1 F) γ (.valid CoPset.full) ⊢ iprop(⌜False⌝) :=
  iOwn_cmraValid_op.trans fun n x h => by
    have h' : ✓{n} ((DisjointLeibnizSet.valid CoPset.full : CoPsetDisjL) • DisjointLeibnizSet.valid CoPset.full) := h
    change ✓{n} (if CoPset.full ## CoPset.full then _ else _) at h'
    rw [if_neg full_not_disj] at h'
    exact h'

/-- Allocate an exclusive token in slot 1. -/
theorem own_full_alloc {F : OFunctorPre} [RFunctorContractive F] [RFunctorAffine F] :
    ⊢ (|==> ∃ γ, iOwn (E := gxElem1 F) γ (.valid CoPset.full) : IProp (GX F)) :=
  iOwn_alloc (E := gxElem1 F) _ trivial

/-- An update to `⌜False⌝` cannot be valid. -/
theorem bupd_false_unsound {GF : BundledGFunctors} (H : ⊢ (|==> iprop(⌜False⌝) : IProp GF)) : False :=
  pure_soundness (PROP := IProp GF) (UPred.bupd_soundness H)

/-- Fancy-update soundness to `▷ False` from `⊤` to any mask. -/
theorem fupd_later_false {GF : BundledGFunctors} [InvGpreS GF] (E2 : CoPset)
    (H : ∀ [InvGS_gen .hasNoLC GF], ⊢ (iprop(|={⊤,E2}=> ▷ ⌜False⌝) : IProp GF)) : False :=
  pure_soundness (PROP := IProp GF)
    (fupd_soundness .hasNoLC 0 (E1 := ⊤) (E2 := E2) (P := iprop(⌜False⌝)) fun _ =>
      wand_intro (sep_elim_left.trans (H.trans
        ((BIFUpdate.mono (or_intro_l (Q := iprop(⌜False⌝)))).trans fupd_except0))))

/-- The exclusive slot-1 resource `valid ⊤` at name `γ`. -/
noncomputable abbrev own1 (F : OFunctorPre) [RFunctorContractive F] [RFunctorAffine F] (γ : GName) : IProp (GX F) :=
  iOwn (E := gxElem1 F) γ (.valid CoPset.full)

open Iris.Std.LawfulSet in
theorem empty_diffN (N : Namespace) : (∅ \ ↑N : CoPset) = ∅ := by
  ext x; rw [mem_diff]; simp [mem_empty]

theorem empty_subsetC (E : CoPset) : (∅ : CoPset) ⊆ E := fun _ h => (CoPset.mem_empty h).elim

/-- Two later copies of the exclusive resource give `▷ False`. -/
theorem dup_later_false {F : OFunctorPre} [RFunctorContractive F] [RFunctorAffine F] (γ : GName) :
    ▷ own1 F γ ∗ ▷ own1 F γ ⊢ ▷ ⌜False⌝ :=
  later_sep.mpr.trans (later_mono (own_full_dup_false γ))

/-- `▷ False` proves any fancy update. -/
theorem later_false_fupd {GF : BundledGFunctors} [InvGS_gen hlc GF] {E1 E2 : CoPset} {X : IProp GF} :
    ▷ ⌜False⌝ ⊢ |={E1,E2}=> X :=
  (or_intro_l (Q := iprop(|={E1,E2}=> X))).trans (except0_fupd.trans fupd_except0)

/-- `⊢ |={⊤|}=> False` under every invariant setup is unsound. -/
theorem ffin_false {GF : BundledGFunctors} [InvGpreS GF]
    (H : ∀ [InvGS_gen .hasNoLC GF], ⊢ (iprop(|={⊤|}=> ⌜False⌝) : IProp GF)) : False :=
  pure_soundness (PROP := IProp GF)
    (fupd_finally_soundness .hasNoLC 0 ⊤ iprop(⌜False⌝) fun _ => true_intro.trans (true_emp.mp.trans H))

/-- `⊢ £ 0 -∗ |==£> False` under every credit setup is unsound. -/
theorem leupd_false {GF : BundledGFunctors} [LcGpreS GF]
    (H : ∀ {_ : LcGS .hasNoLC GF}, ⊢ (iprop(|==£> ⌜False⌝) : IProp GF)) : False :=
  pure_soundness (PROP := IProp GF)
    (lc_soundness .hasNoLC 0 iprop(⌜False⌝) fun {_} => wand_intro (sep_elim_left.trans H))

/-- `⊢ £ 0 -∗ |==£|> False` under every credit setup is unsound. -/
theorem leupdf_false {GF : BundledGFunctors} [LcGpreS GF]
    (H : ∀ [LcGS .hasNoLC GF], ⊢ (iprop(|==£|> ⌜False⌝) : IProp GF)) : False :=
  pure_soundness (PROP := IProp GF)
    (le_upd_finally_soundness .hasNoLC 0 iprop(⌜False⌝) fun {_} => true_intro.trans (true_emp.mp.trans H))

/-- The slot-1 resource `valid ⊤` is not valid in the empty context. -/
theorem own_full_not_valid {F : OFunctorPre} [RFunctorContractive F] [RFunctorAffine F]
    (H : ⊢ (iprop(∃ γ, own1 F γ) : IProp (GX F))) : False :=
  pure_soundness (PROP := IProp (GX F))
    ((persistently_emp_intro.trans (persistently_mono H)).trans
      (persistently_exists.mp.trans (exists_elim fun γ =>
        persistently_sep_persistently.mpr.trans ((sep_mono persistently_elim persistently_elim).trans (own_full_dup_false γ)))))

instance cinvGX : CInvG (GX CInvF) := ⟨gxElem CInvF⟩
instance naInvGX : NaInvG (GX NaInvF) := ⟨gxElem NaInvF⟩

instance gvGX : GhostVarG (GX (GhostVarF Bool)) Bool := ⟨⟩
noncomputable abbrev SPF : OFunctorPre := DFracAgree.DFracAgreeRF (LaterOF IdOF)
instance spGX : SavedPropG (GX SPF) := ⟨⟩
noncomputable abbrev SDF : OFunctorPre := DFracAgree.DFracAgreeRF (DiscreteFunOF (fun _ : Unit => LaterOF IdOF))
instance sdGX : SavedPredG (GX SDF) Unit := ⟨⟩
abbrev TM (V : Type) := Std.ExtTreeMap Nat V compare
noncomputable abbrev GMF : OFunctorPre := constOF (HeapView Nat (Agree (DiscreteO Bool)) TM)
instance gmGX : GhostMapG (GX GMF) Nat Bool TM := ⟨gxElem GMF⟩

/-- `▷ False` under a basic update is unsound. -/
theorem bupd_later_false {GF : BundledGFunctors} (H : ⊢ (|==> ▷ ⌜False⌝ : IProp GF)) : False :=
  pure_soundness (PROP := IProp GF) (UPred.later_soundness (UPred.bupd_soundness H))

/-- Later of the internal equality of `False` and `True` gives `▷ False`. -/
theorem eq_ft_false {GF : BundledGFunctors} :
    (iprop(▷ Iris.internalEq (PROP := IProp GF) (iprop(⌜False⌝) : IProp GF) iprop(⌜True⌝)) : IProp GF) ⊢ ▷ ⌜False⌝ :=
  later_mono ((internalEq_iff (PROP := IProp GF) _ _).trans (and_elim_r.trans (by
    iintro H
    iapply H
    ipureintro
    trivial)))

theorem dq2 : ¬ ✓ (DFrac.own (1 + 1)) := fun h => by
  have : ((1:Qp)+1).val ≤ 1 := h; grind

end W7c0
open Iris Iris.BI W7c0

-- `UPred.uPred_entails_lim` idx 4: necessary (UPred NA, constant chains True and False)
theorem u_1 : ¬ drop0% UPred.uPred_entails_lim 4 := fun h => by
  have H := @h NA _ (Chain.const iprop(True)) (Chain.const iprop(False))
  rw [COFE.compl_const, COFE.compl_const] at H
  exact H 0 ⟨.e, trivial⟩ trivial
-- `UPred.persistently_elim` idx 2: necessary (UPred NA (equality order, not IncOrd), P = ownM e at resource a)
theorem u_2 : ¬ drop0% UPred.persistently_elim 2 := fun h => by
  have H := @h NA _ (UPred.ownM NA.e) 0 ⟨.a, trivial⟩ rfl
  cases H
-- `UPred.instAffineUPredOfIncOrd` idx 2: necessary (UPred NA non-affine: True ⊬ emp at a)
theorem u_3 : ¬ drop0% UPred.instAffineUPredOfIncOrd 2 := fun h => by
  have H := (@h NA _ iprop(True)).affine 0 ⟨.a, trivial⟩ trivial
  cases H
-- `UPred.instBIAffineUPredOfIncOrd` idx 2: necessary (UPred NA non-affine: True ⊬ emp at a)
theorem u_4 : ¬ drop0% UPred.instBIAffineUPredOfIncOrd 2 := fun h => by
  have H := ((@h NA _).affine iprop(True)).affine 0 ⟨.a, trivial⟩ trivial
  cases H
-- `UPred.uPredSiPure_mono` idx 4: necessary (Pi = True, Qi = False)
theorem u_5 : ¬ drop0% UPred.uPredSiPure_mono 4 := fun h =>
  (@h NA _ iprop(True) iprop(False)) 0 ⟨.e, trivial⟩ trivial
-- `UPred.uPredSiEmpValid_mono` idx 4: necessary (P = True, Q = False)
theorem u_6 : ¬ drop0% UPred.uPredSiEmpValid_mono 4 := fun h =>
  (@h NA _ iprop(True) iprop(False)) 0 trivial
-- `UPred.ownM_always_invalid_elim` idx 3: necessary (m = unit (valid))
theorem u_7 : ¬ drop0% UPred.ownM_always_invalid_elim 3 := fun h =>
  (@h NA _ NA.e) 0 ⟨.e, trivial⟩ trivial
-- `UPred.ownM_unit` idx 2: necessary (UPred NA, P = True at resource a: emp fails)
theorem u_8 : ¬ drop0% UPred.ownM_unit 2 := fun h => by
  have H := (@h NA _ iprop(True)) 0 ⟨.a, trivial⟩ trivial
  cases H.1
-- `UPred.intuitionistically_ownM_core` idx 2: necessary (UPred NA, m = a: emp fails at a)
theorem u_9 : ¬ drop0% UPred.intuitionistically_ownM_core 2 := fun h => by
  have H := (@h NA _ NA.a) 0 ⟨.a, trivial⟩ rfl
  cases H.1
-- `UPred.bupd_ownM_updateP` idx 4: necessary (Φ = False)
theorem u_10 : ¬ drop0% UPred.bupd_ownM_updateP 4 := fun h => by
  have H := (@h NA _ NA.e (fun _ => False)) 0 ⟨.e, trivial⟩ rfl 0 NA.e (Nat.le_refl _) trivial
  obtain ⟨_, _, _, ⟨_, rfl⟩, hf, _⟩ := H
  exact hf
-- `UPred.pure_soundness` idx 3: necessary (P = False)
theorem u_12 : ¬ drop0% UPred.pure_soundness 3 := fun h => @h NA _ False
-- `UPred.later_soundness` idx 3: necessary (P = False)
theorem u_13 : ¬ drop0% UPred.later_soundness 3 := fun h =>
  (@h NA _ iprop(False)) 0 ⟨.e, trivial⟩ rfl
-- `UPred.intuitionistically_ownM` idx 3: necessary (UPred AF, ownM a not persistent)
theorem u_14 : ¬ drop0% UPred.intuitionistically_ownM 3 := fun h => by
  have H := (@h AF _ AF.a).2 0 ⟨.a, trivial⟩ (.inr rfl)
  rcases H.2 with h1 | h1 <;> cases h1
-- `UPred.ownM_invalid` idx 3: necessary (a = unit)
theorem u_15 : ¬ drop0% UPred.ownM_invalid 3 := fun h =>
  (@h NA _ NA.e) 0 ⟨.e, trivial⟩ rfl
-- `UPred.ownM_ord_mono` idx 4: necessary (UPred NA, a = e, b = a)
theorem u_16 : ¬ drop0% UPred.ownM_ord_mono 4 := fun h => by
  have H := (@h NA _ NA.e NA.a) 0 ⟨.e, trivial⟩ rfl
  cases H
-- `UPred.ownM_mono` idx 2: necessary (UPred NA (not IncOrd): e ≼ a but ownM a ⊬ ownM e)
theorem u_17 : ¬ drop0% UPred.ownM_mono 2 := fun h => by
  have H := (@h NA _ NA.a NA.e ⟨NA.a, rfl⟩) 0 ⟨.a, trivial⟩ rfl
  cases H
-- `UPred.ownM_mono` idx 5: necessary (UPred AF, a = e, b = a)
theorem u_18 : ¬ drop0% UPred.ownM_mono 5 := fun h => by
  have H := (@h AF _ _ AF.e AF.a) 0 ⟨.e, trivial⟩ (.inl rfl)
  rcases H with h1 | h1 <;> cases h1
-- `UPred.ownM_unit'` idx 2: necessary (UPred NA: True ⊬ ownM unit at a)
theorem u_19 : ¬ drop0% UPred.ownM_unit' 2 := fun h => by
  have H := (@h NA _).2 0 ⟨.a, trivial⟩ trivial
  cases H
-- `UPred.ownM_persistent` idx 3: necessary (UPred AF, ownM a not persistent)
theorem u_22 : ¬ drop0% UPred.ownM_persistent 3 := fun h => by
  have H := (@h AF _ AF.a).persistent 0 ⟨.a, trivial⟩ (.inr rfl)
  rcases H with h1 | h1 <;> cases h1
-- `ownM_updateP` idx 5: necessary (Φ = False, R = False, x = unit)
theorem u_33 : ¬ drop0% ownM_updateP 5 := fun h => by
  have H := (@h NA _ NA.e iprop(False) (fun _ => False)) 0 ⟨.e, trivial⟩
    ⟨NA.e, NA.e, rfl, rfl, by rintro p ⟨y, rfl⟩; exact fun _ _ _ _ hf => hf.elim⟩
  exact H
-- `UPred.discrete_valid` idx 4: necessary (A = VZ (valid only at step 0))
theorem u_31 : ¬ drop0% UPred.discrete_valid 4 := fun h =>
  (@h NA _ VZ _ ⟨true⟩).1 0 ⟨.e, trivial⟩ rfl
-- `UPred.valid_timeless` idx 4: necessary (A = VZ (valid only at step 0): not timeless at step 1)
theorem u_32 : ¬ drop0% UPred.valid_timeless 4 := fun h => by
  have H := (@h NA _ VZ _ ⟨true⟩).timeless 1 ⟨.e, trivial⟩ rfl
  rcases H with H | H
  · exact H
  · exact Nat.succ_ne_zero 0 H
-- `UPred.intuitionistically_valid` idx 2: necessary (UPred NA, a valid: emp fails at a)
theorem u_30 : ¬ drop0% UPred.intuitionistically_valid 2 := fun h => by
  have H := (@h NA _ NA _ NA.e).2 0 ⟨.a, trivial⟩ trivial
  cases H.1

-- `UPred.bupd_ownM_update` idx 4: necessary (UPred TX, x = e, y = z (invalid))
theorem u_20 : ¬ drop0% UPred.bupd_ownM_update 4 := fun h => by
  have H := (@h TX _ TX.e TX.z) 0 ⟨.e, show TX.e ≠ .z by decide⟩ (show TX.e = .z ∨ TX.e ≠ .z by decide) 0 TX.e (Nat.le_refl _) (show TX.e ≠ .z by decide)
  obtain ⟨x', hv, ho⟩ := H
  have ho' : x' = .z ∨ TX.z ≠ .z := ho
  rcases ho' with rfl | h2
  · exact hv rfl
  · exact h2 rfl
-- `UPred.ownM_timeless` idx 3: necessary (UPred TD (non-discrete max UORA), a = 1, x = 0 at step 1)
theorem u_21 : ¬ drop0% UPred.ownM_timeless 3 := fun h => by
  have H := (@h TD _ ⟨1⟩).timeless 1 ⟨⟨0⟩, trivial⟩ (show min 1 0 ≤ min 0 0 by decide)
  rcases H with H | H
  · exact H
  · exact absurd (show min 1 1 ≤ min 0 1 from H) (by decide)
theorem af_bupd_a : ⊢ (BUpd.bupd (UPred.ownM AF.a) : UPred AF) :=
  fun _ _ _ k _ _ _ => ⟨AF.a, trivial, .inr rfl⟩
theorem af_not_a : ¬ (⊢ (UPred.ownM AF.a : UPred AF)) := fun h => by
  rcases h 0 ⟨.e, trivial⟩ (.inl rfl) with h1 | h1 <;> cases h1
-- `UPred.bupd_soundness` idx 3: necessary (UPred AF, P = ownM a: ⊢ |==> ownM a but not ⊢ ownM a)
theorem u_23 : ¬ drop0% UPred.bupd_soundness 3 := fun h => af_not_a (@h AF _ _ af_bupd_a)
-- `UPred.bupd_soundness` idx 4: necessary (P = False)
theorem u_24 : ¬ drop0% UPred.bupd_soundness 4 := fun h =>
  (@h NA _ iprop(False) inferInstance) 0 ⟨.e, trivial⟩ rfl
-- `UPred.modal_soundness` idx 3: necessary (UPred AF, ms = [bupd], P = ownM a)
theorem u_28 : ¬ drop0% UPred.modal_soundness 3 := fun h => af_not_a (@h AF _ _ [.bupd] af_bupd_a)
-- `UPred.modal_soundness` idx 5: necessary (P = False, ms = [])
theorem u_29 : ¬ drop0% UPred.modal_soundness 5 := fun h =>
  (@h NA _ iprop(False) inferInstance []) 0 ⟨.e, trivial⟩ rfl
-- `_private.Iris.Instances.UPred.Instance.0.UPred.Modality.denoteAll_plainly_laterN` idx 3: necessary (UPred AF, ms = [], P = ownM a not plain)
theorem u_25 : ¬ drop0% _private.Iris.Instances.UPred.Instance.«0».UPred.Modality.denoteAll_plainly_laterN 3 := fun h => by
  have H := (@h AF _ (UPred.ownM AF.a) []) 0 ⟨.a, trivial⟩ (.inr rfl)
  rcases H with h1 | h1 <;> cases h1
instance naEmpPlain : Plain (UPred.ownM NA.e : UPred NA) := ⟨fun _ _ _ => (rfl : NA.e = NA.e)⟩
-- `UPred.Modality.denoteAll_laterN` idx 2: necessary (UPred NA, P = emp (plain), ms = [persistently], step 1 at a)
theorem u_26 : ¬ drop0% UPred.Modality.denoteAll_laterN 2 := fun h => by
  have H := (@h NA _ (UPred.ownM NA.e) naEmpPlain [.persistently]) 1 ⟨.a, trivial⟩ (rfl : NA.e = NA.e)
  cases H
-- `UPred.Modality.denoteAll_laterN` idx 4: necessary (UPred AF, P = ownM a, ms = [bupd], step 1 at unit)
theorem u_27 : ¬ drop0% UPred.Modality.denoteAll_laterN 4 := fun h => by
  have H := (@h AF _ _ (UPred.ownM AF.a) [.bupd]) 1 ⟨.e, trivial⟩ (af_bupd_a 1 ⟨.e, trivial⟩ (.inl rfl))
  rcases H with h1 | h1 <;> cases h1

-- `Iris.token_alloc_strong` idx 3: necessary (P = False: |==> False)
theorem t_tok : ¬ drop0% Iris.token_alloc_strong 3 := fun h =>
  bupd_false_unsound ((@h (GX TokenF) { elemG := gxElem TokenF } (fun _ => False)).trans
    (BIUpdate.mono (exists_elim fun _ => sep_elim_left)))

-- `Iris.inv_acc` idx 6: necessary (IProp over GX (closed-proofs slots + one user functor); exclusive valid ⊤ in slot 1; E = ∅: opening the invariant twice gives two copies of the exclusive resource (▷ False), fupd_soundness)
theorem t_inv : ¬ drop0% Iris.inv_acc 6 := fun h =>
  fupd_later_false (GF := GX TokenF) ((∅ \ ↑nroot) \ ↑nroot) fun {_} => by
    iintro
    imod own_full_alloc (F := TokenF) with ⟨%γ, Ho⟩
    imod inv_alloc nroot ⊤ (iOwn (E := gxElem1 TokenF) γ (.valid CoPset.full)) $$ [Ho] with #Hinv
    · inext; iexact Ho
    imod fupd_mask_subseteq (E1 := ⊤) (E2 := ∅) (fun _ h => (CoPset.mem_empty h).elim) with _
    imod h (E := ∅) (N := nroot) $$ Hinv with ⟨H1, _⟩
    imod h (E := ∅ \ ↑nroot) (N := nroot) $$ Hinv with ⟨H2, _⟩
    imodintro
    inext
    iapply own_full_dup_false γ
    isplitl [H1]
    · iexact H1
    · iexact H2

-- `Iris.own_inv_acc` idx 6: necessary (IProp over GX (closed-proofs slots + one user functor); exclusive valid ⊤ in slot 1; E = ∅: opening the invariant twice gives two copies of the exclusive resource (▷ False), fupd_soundness)
theorem t_own_inv_acc : ¬ drop0% Iris.own_inv_acc 6 := fun h =>
  fupd_later_false (GF := GX TokenF) ((∅ \ ↑nroot) \ ↑nroot) fun {_} => by
    iintro
    imod own_full_alloc (F := TokenF) with ⟨%γ, Ho⟩
    imod own_inv_alloc nroot ⊤ (own1 TokenF γ) $$ [Ho] with #Hinv
    · inext; iexact Ho
    imod fupd_mask_subseteq (E1 := ⊤) (E2 := ∅) (empty_subsetC _) with _
    imod h ∅ nroot _ $$ Hinv with ⟨H1, _⟩
    imod h (∅ \ ↑nroot) nroot _ $$ Hinv with ⟨H2, _⟩
    imodintro
    inext
    iapply own_full_dup_false γ
    isplitl [H1]
    · iexact H1
    · iexact H2

-- `Iris.inv_acc_strong` idx 6: necessary (IProp over GX (closed-proofs slots + one user functor); exclusive valid ⊤ in slot 1; E = ∅: opening the invariant twice gives two copies of the exclusive resource (▷ False), fupd_soundness)
theorem t_inv_acc_strong : ¬ drop0% Iris.inv_acc_strong 6 := fun h =>
  fupd_later_false (GF := GX TokenF) ((∅ \ ↑nroot) \ ↑nroot) fun {_} => by
    iintro
    imod own_full_alloc (F := TokenF) with ⟨%γ, Ho⟩
    imod inv_alloc nroot ⊤ (own1 TokenF γ) $$ [Ho] with #Hinv
    · inext; iexact Ho
    imod fupd_mask_subseteq (E1 := ⊤) (E2 := ∅) (empty_subsetC _) with _
    imod h (E := ∅) (N := nroot) $$ Hinv with ⟨H1, _⟩
    imod h (E := ∅ \ ↑nroot) (N := nroot) $$ Hinv with ⟨H2, _⟩
    imodintro
    inext
    iapply own_full_dup_false γ
    isplitl [H1]
    · iexact H1
    · iexact H2

-- `Iris.inv_alloc_open` idx 6: necessary (E = ∅ (∅ \ N = ∅): inv N False for free, then open at ⊤ gives ▷ False)
theorem t_inv_alloc_open : ¬ drop0% Iris.inv_alloc_open 6 := fun h =>
  fupd_later_false (GF := GX TokenF) (⊤ \ ↑nroot) fun {_} => by
    iintro
    imod fupd_mask_subseteq (E1 := ⊤) (E2 := ∅) (empty_subsetC _) with Hcl
    imod h nroot ∅ iprop(⌜False⌝) with ⟨#Hinv, _⟩
    rw [empty_diffN]
    imod Hcl
    imod inv_acc (E := ⊤) (N := nroot) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨H1, _⟩
    imodintro
    iexact H1

-- `Iris.own_inv_alloc_open` idx 6: necessary (E = ∅ (∅ \ N = ∅): own_inv N False for free, then open at ⊤ gives ▷ False)
theorem t_own_inv_alloc_open : ¬ drop0% Iris.own_inv_alloc_open 6 := fun h =>
  fupd_later_false (GF := GX TokenF) (⊤ \ ↑nroot) fun {_} => by
    iintro
    imod fupd_mask_subseteq (E1 := ⊤) (E2 := ∅) (empty_subsetC _) with Hcl
    imod h nroot ∅ iprop(⌜False⌝) with ⟨#Hinv, _⟩
    rw [empty_diffN]
    imod Hcl
    imod own_inv_acc ⊤ nroot _ (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨H1, _⟩
    imodintro
    iexact H1

-- `Iris.inv_acc_timeless` idx 7: necessary (IProp over GX (closed-proofs slots + one user functor); exclusive valid ⊤ in slot 1; E = ∅: opening the invariant twice gives two copies of the exclusive resource (▷ False), fupd_soundness)
theorem t_inv_acc_timeless7 : ¬ drop0% Iris.inv_acc_timeless 7 := fun h =>
  fupd_later_false (GF := GX TokenF) ((∅ \ ↑nroot) \ ↑nroot) fun {_} => by
    iintro
    imod own_full_alloc (F := TokenF) with ⟨%γ, Ho⟩
    imod inv_alloc nroot ⊤ (own1 TokenF γ) $$ [Ho] with #Hinv
    · inext; iexact Ho
    imod fupd_mask_subseteq (E1 := ⊤) (E2 := ∅) (empty_subsetC _) with _
    imod h (E := ∅) (N := nroot) $$ Hinv with ⟨H1, _⟩
    imod h (E := ∅ \ ↑nroot) (N := nroot) $$ Hinv with ⟨H2, _⟩
    imodintro
    inext
    iapply own_full_dup_false γ
    isplitl [H1]
    · iexact H1
    · iexact H2

open CancelableInvariant in
-- `Iris.CancelableInvariant.acc` idx 9: necessary (IProp over GX (closed-proofs slots + one user functor); exclusive valid ⊤ in slot 1; E = ∅: opening the invariant twice gives two copies of the exclusive resource (▷ False), fupd_soundness (own γ 1 returned))
theorem c_acc : ¬ drop0% Iris.CancelableInvariant.acc 9 := fun h =>
  fupd_later_false (GF := GX CInvF) ((∅ \ ↑nroot) \ ↑nroot) fun {_} => by
    iintro
    imod own_full_alloc (F := CInvF) with ⟨%γ0, Ho⟩
    imod CancelableInvariant.alloc ⊤ nroot (own1 CInvF γ0) $$ [Ho] with ⟨%γ, #Hinv, Hown⟩
    · inext; iexact Ho
    imod fupd_mask_subseteq (E1 := ⊤) (E2 := ∅) (empty_subsetC _) with _
    imod h (E := ∅) (N := nroot) (γ := γ) (p := 1) $$ Hinv Hown with ⟨H1, Hown, _⟩
    imod h (E := ∅ \ ↑nroot) (N := nroot) (γ := γ) (p := 1) $$ Hinv Hown with ⟨H2, _, _⟩
    imodintro
    iapply dup_later_false γ0
    isplitl [H1]
    · iexact H1
    · iexact H2

-- `Iris.CancelableInvariant.acc_strong` idx 9: necessary (IProp over GX (closed-proofs slots + one user functor); exclusive valid ⊤ in slot 1; E = ∅: opening the invariant twice gives two copies of the exclusive resource (▷ False), fupd_soundness (own γ 1 returned))
theorem c_acc_strong : ¬ drop0% Iris.CancelableInvariant.acc_strong 9 := fun h =>
  fupd_later_false (GF := GX CInvF) ((∅ \ ↑nroot) \ ↑nroot) fun {_} => by
    iintro
    imod own_full_alloc (F := CInvF) with ⟨%γ0, Ho⟩
    imod CancelableInvariant.alloc ⊤ nroot (own1 CInvF γ0) $$ [Ho] with ⟨%γ, #Hinv, Hown⟩
    · inext; iexact Ho
    imod fupd_mask_subseteq (E1 := ⊤) (E2 := ∅) (empty_subsetC _) with _
    imod h ∅ nroot γ 1 _ $$ Hinv Hown with ⟨H1, Hown, _⟩
    imod h (∅ \ ↑nroot) nroot γ 1 _ $$ Hinv Hown with ⟨H2, _, _⟩
    imodintro
    iapply dup_later_false γ0
    isplitl [H1]
    · iexact H1
    · iexact H2

-- `Iris.CancelableInvariant.cancel` idx 8: necessary (open with acc at ⊤, then cancel at ⊤ \ N: two copies of the exclusive resource)
theorem c_cancel : ¬ drop0% Iris.CancelableInvariant.cancel 8 := fun h =>
  fupd_later_false (GF := GX CInvF) (⊤ \ ↑nroot) fun {_} => by
    iintro
    imod own_full_alloc (F := CInvF) with ⟨%γ0, Ho⟩
    imod CancelableInvariant.alloc ⊤ nroot (own1 CInvF γ0) $$ [Ho] with ⟨%γ, #Hinv, Hown⟩
    · inext; iexact Ho
    imod CancelableInvariant.acc (E := ⊤) (p := 1) (fun _ _ => CoPset.mem_full) $$ Hinv Hown with ⟨H1, Hown, _⟩
    imod h (⊤ \ ↑nroot) $$ Hinv Hown with H2
    imodintro
    iapply dup_later_false γ0
    isplitl [H1]
    · iexact H1
    · iexact H2

-- `Iris.CancelableInvariant.acc_one` idx 8: necessary (open with acc at ⊤, then acc_one at ⊤ \ N: two copies of the exclusive resource)
theorem c_acc_one : ¬ drop0% Iris.CancelableInvariant.acc_one 8 := fun h =>
  fupd_later_false (GF := GX CInvF) (⊤ \ ↑nroot) fun {_} => by
    iintro
    imod own_full_alloc (F := CInvF) with ⟨%γ0, Ho⟩
    imod CancelableInvariant.alloc ⊤ nroot (own1 CInvF γ0) $$ [Ho] with ⟨%γ, #Hinv, Hown⟩
    · inext; iexact Ho
    imod CancelableInvariant.acc (E := ⊤) (p := 1) (fun _ _ => CoPset.mem_full) $$ Hinv Hown with ⟨H1, Hown, _⟩
    imod h (⊤ \ ↑nroot) nroot γ _ $$ Hinv Hown with ⟨H2, _⟩
    imodintro
    iapply dup_later_false γ0
    isplitl [H1]
    · iexact H1
    · iexact H2

-- `Iris.CancelableInvariant.alloc_open` idx 7: necessary (E = ∅: cinv N γ False for free, then acc at ⊤ gives ▷ False)
theorem c_alloc_open : ¬ drop0% Iris.CancelableInvariant.alloc_open 7 := fun h =>
  fupd_later_false (GF := GX CInvF) (⊤ \ ↑nroot) fun {_} => by
    iintro
    imod fupd_mask_subseteq (E1 := ⊤) (E2 := ∅) (empty_subsetC _) with Hcl
    imod h ∅ nroot iprop(⌜False⌝) with ⟨%γ, #Hinv, Hown, _⟩
    rw [empty_diffN]
    imod Hcl
    imod CancelableInvariant.acc (E := ⊤) (p := 1) (fun _ _ => CoPset.mem_full) $$ Hinv Hown with ⟨H1, _, _⟩
    imodintro
    iexact H1

-- `Iris.CancelableInvariant.alloc_strong_open` idx 8: necessary (E = ∅, P = True: cinv N γ False for free, then acc at ⊤ gives ▷ False)
theorem c_alloc_strong_open : ¬ drop0% Iris.CancelableInvariant.alloc_strong_open 8 := fun h =>
  fupd_later_false (GF := GX CInvF) (⊤ \ ↑nroot) fun {_} => by
    iintro
    imod fupd_mask_subseteq (E1 := ⊤) (E2 := ∅) (empty_subsetC _) with Hcl
    imod h (fun _ => True) PredInfinite.true ∅ nroot with ⟨%γ, _, Hown, Hall⟩
    imod Hall $$ %iprop(⌜False⌝) with ⟨#Hinv, _⟩
    rw [empty_diffN]
    imod Hcl
    imod CancelableInvariant.acc (E := ⊤) (p := 1) (fun _ _ => CoPset.mem_full) $$ Hinv Hown with ⟨H1, _, _⟩
    imodintro
    iexact H1

-- `Iris.CancelableInvariant.inv_open_fupd` idx 11: necessary (open with acc at ⊤, then E = ⊤ \ N, Q = ▷ P: the wand gets two copies, R = False)
theorem c_inv_open_fupd : ¬ drop0% Iris.CancelableInvariant.inv_open_fupd 11 := fun h =>
  fupd_later_false (GF := GX CInvF) (⊤ \ ↑nroot) fun {_} => by
    iintro
    imod own_full_alloc (F := CInvF) with ⟨%γ0, Ho⟩
    imod CancelableInvariant.alloc ⊤ nroot (own1 CInvF γ0) $$ [Ho] with ⟨%γ, #Hinv, Hown⟩
    · inext; iexact Ho
    imod CancelableInvariant.acc (E := ⊤) (p := 1) (fun _ _ => CoPset.mem_full) $$ Hinv Hown with ⟨H1, Hown, _⟩
    imod h (E := ⊤ \ ↑nroot) (Q := iprop(▷ own1 CInvF γ0)) (R := iprop(⌜False⌝)) (q := 1) $$ Hinv [] [H1 Hown] with HF
    · iintro ⟨H2, H3, _⟩
      iapply later_false_fupd
      iapply dup_later_false γ0
      isplitl [H2]
      · iexact H2
      · iexact H3
    · isplitl [H1]
      · iexact H1
      · iexact Hown
    imodintro
    inext
    iexact HF

-- `Iris.CancelableInvariant.own_excl_alloc` idx 3: necessary (P = False)
theorem c_own_excl_alloc : ¬ drop0% Iris.CancelableInvariant.own_excl_alloc 3 := fun h =>
  bupd_false_unsound ((h (GF := GX CInvF) (fun _ => False)).trans
    (BIUpdate.mono (exists_elim fun _ => sep_elim_left)))

-- `Iris.CancelableInvariant.alloc_strong` idx 5: necessary (P = False, fupd_soundness)
theorem c_alloc_strong : ¬ drop0% Iris.CancelableInvariant.alloc_strong 5 := fun h =>
  fupd_later_false (GF := GX CInvF) ⊤ fun {_} =>
    (h (fun _ => False) ⊤ nroot).trans (BIFUpdate.mono (exists_elim fun _ => sep_elim_left.trans later_intro))

-- `Iris.CancelableInvariant.alloc_strong_open` idx 5: necessary (P = False, fupd_soundness)
theorem c_alloc_strong_open5 : ¬ drop0% Iris.CancelableInvariant.alloc_strong_open 5 := fun h =>
  fupd_later_false (GF := GX CInvF) ⊤ fun {_} =>
    (h (fun _ => False) ⊤ nroot (fun _ _ => CoPset.mem_full)).trans
      (BIFUpdate.mono (exists_elim fun _ => sep_elim_left.trans later_intro))

-- `Iris.inv_open_fupd` idx 8: necessary (IProp over GX (closed-proofs slots + one user functor); exclusive valid ⊤ in slot 1; open inv at ⊤, then E = ⊤ \ N with Q = ▷ P: the wand gets two copies (▷ False), R = False)
theorem i_open_fupd : ¬ drop0% Iris.inv_open_fupd 8 := fun h =>
  fupd_later_false (GF := GX TokenF) (⊤ \ ↑nroot) fun {_} => by
    iintro
    imod own_full_alloc (F := TokenF) with ⟨%γ0, Ho⟩
    imod inv_alloc nroot ⊤ (own1 TokenF γ0) $$ [Ho] with #Hinv
    · inext; iexact Ho
    imod inv_acc (E := ⊤) (N := nroot) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨H1, _⟩
    imod h (E := ⊤ \ ↑nroot) (Q := iprop(▷ own1 TokenF γ0)) (R := iprop(⌜False⌝)) $$ Hinv [] H1 with HF
    · iintro ⟨H2, H3⟩
      iapply later_false_fupd
      iapply dup_later_false γ0
      isplitl [H2]
      · iexact H2
      · iexact H3
    imodintro
    inext
    iexact HF

-- `Iris.inv_combine` idx 8: necessary (N1 = N2 = N = nroot: inv N P twice gives inv N (P ∗ P) with P exclusive)
theorem i_combine8 : ¬ drop0% Iris.inv_combine 8 := fun h =>
  fupd_later_false (GF := GX TokenF) (⊤ \ ↑nroot) fun {_} => by
    iintro
    imod own_full_alloc (F := TokenF) with ⟨%γ0, Ho⟩
    imod inv_alloc nroot ⊤ (own1 TokenF γ0) $$ [Ho] with #Hinv
    · inext; iexact Ho
    ihave #H2 := h nroot nroot nroot _ _ (fun _ hx => by
      rcases Iris.Std.LawfulSet.mem_union.mp hx with h1 | h1 <;> exact h1) $$ Hinv Hinv
    imod inv_acc (E := ⊤) (N := nroot) (fun _ _ => CoPset.mem_full) $$ H2 with ⟨H1, _⟩
    imodintro
    iapply dup_later_false γ0
    iapply later_sep.mp
    iexact H1

-- `Iris.fupd_soundness` idx 8: necessary (P = False)
theorem f_sound8 : ¬ drop0% Iris.fupd_soundness 8 := fun h =>
  pure_soundness (PROP := IProp (GX TokenF)) (h .hasNoLC 0 (E1 := ⊤) (E2 := ⊤) (P := iprop(⌜False⌝)))
-- `Iris.step_fupdN_soundness` idx 7: necessary (P = False)
theorem f_step7 : ¬ drop0% Iris.step_fupdN_soundness 7 := fun h =>
  pure_soundness (PROP := IProp (GX TokenF)) (h (hlc := .hasNoLC) 0 0 (P := iprop(⌜False⌝)))
-- `Iris.step_fupdN_soundness_close` idx 7: necessary (P = False)
theorem f_stepc7 : ¬ drop0% Iris.step_fupdN_soundness_close 7 := fun h =>
  pure_soundness (PROP := IProp (GX TokenF)) (h (hlc := .hasNoLC) 0 0 (P := iprop(⌜False⌝)))
-- `Iris.le_upd_finally_soundness` idx 5: necessary (P = False)
theorem l_fin_sound : ¬ drop0% Iris.le_upd_finally_soundness 5 := fun h =>
  pure_soundness (PROP := IProp (GX TokenF)) (h .hasNoLC 0 iprop(⌜False⌝))
-- `Iris.lc_soundness` idx 6: necessary (P = False)
theorem l_sound6 : ¬ drop0% Iris.lc_soundness 6 := fun h =>
  pure_soundness (PROP := IProp (GX TokenF)) (h .hasNoLC 0 iprop(⌜False⌝))

theorem fin_true {GF : BundledGFunctors} [InvGS_gen hlc GF] {E : CoPset} : ⊢ (iprop(|={E|}=> ⌜True⌝) : IProp GF) :=
  (pure_intro trivial).trans (plainly_pure.mpr.trans (fupd_finally_intro E _))
theorem leupd_true {GF : BundledGFunctors} [LcGS hlc GF] : ⊢ (iprop(|==£> ⌜True⌝) : IProp GF) :=
  (pure_intro trivial).trans le_upd_intro
theorem leupdf_true {GF : BundledGFunctors} [LcGS hlc GF] : ⊢ (iprop(|==£|> ⌜True⌝) : IProp GF) :=
  (pure_intro trivial).trans (plainly_pure.mpr.trans (le_upd_finally_intro _))
theorem fupd_true {GF : BundledGFunctors} [InvGS_gen hlc GF] {E : CoPset} : ⊢ (iprop(|={E}=> ⌜True⌝) : IProp GF) :=
  (pure_intro trivial).trans fupd_intro

-- `Iris.fupd_finally_mono` idx 6: necessary (P = True, Q = False, fupd_finally_soundness)
theorem f_fin_mono : ¬ drop0% Iris.fupd_finally_mono 6 := fun h =>
  ffin_false (GF := GX TokenF) fun {_} => fin_true.trans (h (E := ⊤) (P := iprop(⌜True⌝)) (Q := iprop(⌜False⌝)))
-- `Iris.fromForall_fupd_finally` idx 7: necessary (A = True, Φ = True, P = False, fupd_finally_soundness)
theorem f_fromForall_fin : ¬ drop0% Iris.fromForall_fupd_finally 7 := fun h =>
  ffin_false (GF := GX TokenF) fun {_} =>
    (forall_intro fun _ => fin_true).trans (h (A := True) ⊤ iprop(⌜False⌝) (fun _ => iprop(⌜True⌝))).from_forall
-- `Iris.fromPure_fupd_finally` idx 8: necessary (a = false, φ = True, P = False, fupd_finally_soundness)
theorem f_fromPure_fin : ¬ drop0% Iris.fromPure_fupd_finally 8 := fun h =>
  ffin_false (GF := GX TokenF) fun {_} =>
    (pure_intro trivial).trans (h (io := .out) false ⊤ iprop(⌜False⌝) True).from_pure
-- `Iris.fromForall_fupd_pure` idx 8: necessary (A = Unit, Φ = True, φ = True, P = False, fupd_soundness)
theorem f_fromForall_pure8 : ¬ drop0% Iris.fromForall_fupd_pure 8 := fun h =>
  fupd_later_false (GF := GX TokenF) ⊤ fun {_} =>
    ((forall_intro fun _ => fupd_true).trans (h (A := Unit) ⊤ iprop(⌜False⌝) (fun _ => iprop(⌜True⌝)) (fun _ => True)).from_forall).trans
      (BIFUpdate.mono later_intro)
-- `Iris.fromForall_fupd_pure` idx 9: necessary (A = Unit, Φ = False (FromForall False Φ holds), φ = True, P = False)
theorem f_fromForall_pure9 : ¬ drop0% Iris.fromForall_fupd_pure 9 := fun h =>
  fupd_later_false (GF := GX TokenF) ⊤ fun {_} =>
    ((forall_intro fun _ => fupd_true).trans (h (A := Unit) ⊤ iprop(⌜False⌝) (fun _ => iprop(⌜False⌝)) (fun _ => True)
      (h := ⟨forall_elim ()⟩)).from_forall).trans (BIFUpdate.mono later_intro)
-- `Iris.le_upd_mono` idx 5: necessary (P = True, Q = False, lc_soundness)
theorem l_mono : ¬ drop0% Iris.le_upd_mono 5 := fun h =>
  leupd_false (GF := GX TokenF) fun {_} => leupd_true.trans (h (P := iprop(⌜True⌝)) (Q := iprop(⌜False⌝)))
-- `Iris.le_upd_finally_mono` idx 5: necessary (P = True, Q = False, le_upd_finally_soundness)
theorem l_fin_mono : ¬ drop0% Iris.le_upd_finally_mono 5 := fun h =>
  leupdf_false (GF := GX TokenF) fun {_} => leupdf_true.trans (h iprop(⌜True⌝) iprop(⌜False⌝))
-- `Iris.from_assumption_le_upd` idx 7: necessary (p = false, P = True, Q = False)
theorem l_from_assumption : ¬ drop0% Iris.from_assumption_le_upd 7 := fun h =>
  leupd_false (GF := GX TokenF) fun {_} =>
    (pure_intro trivial).trans (h (ioP := .out) (p := false) (P := iprop(⌜True⌝)) (Q := iprop(⌜False⌝))).from_assumption
-- `Iris.instFromPureIPropLe_upd` idx 7: necessary (a = false, φ = True, P = False)
theorem l_from_pure : ¬ drop0% Iris.instFromPureIPropLe_upd 7 := fun h =>
  leupd_false (GF := GX TokenF) fun {_} =>
    (pure_intro trivial).trans (h (a := false) (io := .out) (φ := True) (P := iprop(⌜False⌝))).from_pure
-- `Iris.instFrameIPropLe_upd` idx 7: necessary (p = false, R = Q = True, P = False)
theorem l_frame : ¬ drop0% Iris.instFrameIPropLe_upd 7 := fun h =>
  leupd_false (GF := GX TokenF) fun {_} =>
    (sep_emp.mpr.trans (sep_mono (pure_intro (φ := True) trivial) leupd_true)).trans
      (h (p := false) (P := iprop(⌜False⌝)) (R := iprop(⌜True⌝)) (Q := iprop(⌜True⌝))).frame

-- `Iris.lc_soundness` idx 5: necessary (P = ∃ γ, own γ (valid ⊤): allocatable, not valid (its persistent duplicate is invalid))
theorem l_sound5 : ¬ drop0% Iris.lc_soundness 5 := fun h =>
  own_full_not_valid (F := TokenF) (h .hasNoLC 0 _ fun {_} =>
    wand_intro (sep_elim_left.trans ((own_full_alloc (F := TokenF)).trans bupd_le_upd)))

-- `Iris.step_fupdN_soundness` idx 6: necessary (n = 0, P = ∃ γ, own γ (valid ⊤): allocatable, not valid)
theorem f_step6 : ¬ drop0% Iris.step_fupdN_soundness 6 := fun h =>
  own_full_not_valid (F := TokenF) (h (hlc := .hasNoLC) 0 0 fun _ => by
    iintro _
    imod own_full_alloc (F := TokenF) with H
    iapply fupd_mask_intro_discard (empty_subsetC ⊤)
    simp only [step_fupdN]
    iexact H)

-- `Iris.step_fupdN_soundness_close` idx 6: necessary (n = 1, P = ∃ γ, own γ (valid ⊤): allocatable, not valid)
theorem f_stepc6 : ¬ drop0% Iris.step_fupdN_soundness_close 6 := fun h =>
  own_full_not_valid (F := TokenF) (h (hlc := .hasNoLC) 1 0 fun _ => by
    iintro _
    simp only [step_fupdN]
    imod own_full_alloc (F := TokenF) with H
    iapply fupd_mask_intro (empty_subsetC ⊤)
    iintro Hcl
    inext
    imod Hcl
    imodintro
    iexact H)

-- `Iris.NonAtomicInvariant.own_union` idx 5: necessary (E1 = E2 = ⊤: own p ⊤ twice is not disjoint)
theorem n_union : ¬ drop0% Iris.NonAtomicInvariant.own_union 5 := fun h =>
  bupd_false_unsound (GF := GX NaInvF) (by
    iintro
    imod NonAtomicInvariant.alloc with ⟨%p, Hp⟩
    have H2 := (h (GF := GX NaInvF) (p := p) (E1 := ⊤) (E2 := ⊤)).mp
    rw [show (⊤ ∪ ⊤ : CoPset) = ⊤ from rfl] at H2
    ihave H := H2 $$ Hp
    icases H with ⟨H1, H2⟩
    ihave %Hd := NonAtomicInvariant.own_disjoint $$ H1 H2
    exact (full_not_disj Hd).elim)

-- `Iris.NonAtomicInvariant.own_acc` idx 5: necessary (E1 = ∅, E2 = ⊤: own p ∅ gives a second own p ⊤)
theorem n_acc : ¬ drop0% Iris.NonAtomicInvariant.own_acc 5 := fun h =>
  bupd_false_unsound (GF := GX NaInvF) (by
    iintro
    imod NonAtomicInvariant.alloc with ⟨%p, Hp⟩
    imod NonAtomicInvariant.own_empty p with He
    ihave H := h (E2 := ⊤) (E1 := ∅) (tid := p) $$ He
    icases H with ⟨H1, _⟩
    ihave %Hd := NonAtomicInvariant.own_disjoint $$ Hp H1
    exact (full_not_disj Hd).elim)

-- `Iris.NonAtomicInvariant.inv_acc` idx 10: necessary (real opening at F = ⊤, then F = ⊤ \ N: two copies of the exclusive resource)
theorem n_inv_acc10 : ¬ drop0% Iris.NonAtomicInvariant.inv_acc 10 := fun h =>
  fupd_later_false (GF := GX NaInvF) ⊤ fun {_} => by
    iintro
    imod own_full_alloc (F := NaInvF) with ⟨%γ0, Ho⟩
    imod NonAtomicInvariant.alloc with ⟨%p, Hp⟩
    imod NonAtomicInvariant.inv_alloc (p := p) (E := ⊤) (N := nroot) (P := own1 NaInvF γ0) $$ [Ho] with #Hinv
    · inext; iexact Ho
    imod NonAtomicInvariant.inv_acc (E := ⊤) (F := ⊤) (fun _ _ => CoPset.mem_full) (fun _ _ => CoPset.mem_full) $$ Hinv Hp with ⟨H1, Hp, _⟩
    imod h (E := ⊤) (F := ⊤ \ ↑nroot) (N := nroot) (fun _ _ => CoPset.mem_full) $$ Hinv Hp with ⟨H2, _, _⟩
    imodintro
    iapply dup_later_false γ0
    isplitl [H1]
    · iexact H1
    · iexact H2

-- `Iris.ownE_op` idx 4: necessary (E1 = E2 = ⊤ after wsat_alloc: ownE ⊤ twice not disjoint)
theorem w_ownE : ¬ drop0% Iris.ownE_op 4 := fun h =>
  bupd_false_unsound ((wsat_alloc (GF := GX TokenF)).trans (BIUpdate.mono (exists_elim fun W =>
    sep_elim_right.trans ((h (W := W) (E1 := ⊤) (E2 := ⊤)).mp.trans (ownE_disjoint.trans (pure_mono full_not_disj))))))

-- `Iris.ownI_alloc` idx 4: necessary (φ = False)
theorem w_ownI_alloc : ¬ drop0% Iris.ownI_alloc 4 := fun h =>
  bupd_false_unsound (GF := GX TokenF) (by
    iintro
    imod wsat_alloc (GF := GX TokenF) with ⟨%W, Hw, _⟩
    imod h (W := W) (fun _ => False) iprop(⌜True⌝) $$ [Hw] with ⟨%i, %Hf, _⟩
    · isplitl [Hw]
      · iexact Hw
      · inext; ipureintro; trivial
    exact Hf.elim)

-- `Iris.ownI_alloc_open` idx 4: necessary (φ = False)
theorem w_ownI_alloc_open : ¬ drop0% Iris.ownI_alloc_open 4 := fun h =>
  bupd_false_unsound (GF := GX TokenF) (by
    iintro
    imod wsat_alloc (GF := GX TokenF) with ⟨%W, Hw, _⟩
    imod h (W := W) (fun _ => False) iprop(⌜True⌝) $$ Hw with ⟨%i, %Hf, _⟩
    exact Hf.elim)

-- `Iris.ownD_op` idx 4: necessary (E1 = E2 = {i} from ownI_alloc_open: ownD {i} twice)
theorem w_ownD : ¬ drop0% Iris.ownD_op 4 := fun h =>
  bupd_false_unsound (GF := GX TokenF) (by
    iintro
    imod wsat_alloc (GF := GX TokenF) with ⟨%W, Hw, _⟩
    imod ownI_alloc_open (W := W) (· ∈ (↑nroot : CoPset)) iprop(⌜True⌝) (fun E => fresh_name E nroot) $$ Hw with ⟨%i, _, _, _, HD⟩
    have H2 := (h (W := W) (E1 := ({i} : PosSet)) (E2 := {i})).mp
    rw [Iris.Std.LawfulSet.union_idem] at H2
    ihave H := H2 $$ HD
    imodintro
    iapply ownD_singleton_twice
    iexact H)

-- `Iris.inv_combine` idx 9: necessary (N1 = nroot.@1, N2 = N = nroot.@2: inv N2 (P ∗ True) and inv N1 P with P exclusive open together)
theorem i_combine9 : ¬ drop0% Iris.inv_combine 9 := fun h =>
  have Hd : (nroot.@(1 : Nat)) ## (nroot.@(2 : Nat)) := ndot_ne_disjoint nroot (by decide)
  fupd_later_false (GF := GX TokenF) ((⊤ \ ↑(nroot.@(1 : Nat))) \ ↑(nroot.@(2 : Nat))) fun {_} => by
    iintro
    imod own_full_alloc (F := TokenF) with ⟨%γ0, Ho⟩
    imod inv_alloc (nroot.@(1 : Nat)) ⊤ (own1 TokenF γ0) $$ [Ho] with #Hinv
    · inext; iexact Ho
    imod inv_alloc (nroot.@(2 : Nat)) ⊤ iprop(⌜True⌝) $$ [] with #Hinv2
    · inext; ipureintro; trivial
    ihave #H2 := h (nroot.@(1 : Nat)) (nroot.@(2 : Nat)) (nroot.@(2 : Nat)) _ _ Hd $$ Hinv Hinv2
    imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨H1, _⟩
    imod inv_acc (E := ⊤ \ ↑(nroot.@(1 : Nat))) (fun x hx => Iris.Std.LawfulSet.mem_diff.mpr ⟨CoPset.mem_full, fun h1 => Hd x ⟨h1, hx⟩⟩) $$ H2 with ⟨H3, _⟩
    imodintro
    iapply dup_later_false γ0
    isplitl [H1]
    · iexact H1
    · iapply later_mono sep_elim_left
      iexact H3

-- `Iris.saved_anything_alloc_strong` idx 7: necessary (dq = own (1+1) invalid, I = True)
theorem s_any_strong7 : ¬ drop0% Iris.saved_anything_alloc_strong 7 := fun h =>
  bupd_false_unsound ((h (GF := GX SPF) (F := LaterOF IdOF) (Later.next iprop(True)) (fun _ => True) (.own (1 + 1)) PredInfinite.true).trans
    (BIUpdate.mono (exists_elim fun γ => sep_elim_right.trans ((saved_anything_valid γ _ _).trans (pure_mono dq2)))))
-- `Iris.saved_anything_alloc_strong` idx 8: necessary (I = False)
theorem s_any_strong8 : ¬ drop0% Iris.saved_anything_alloc_strong 8 := fun h =>
  bupd_false_unsound ((h (GF := GX SPF) (F := LaterOF IdOF) (Later.next iprop(True)) (fun _ => False) (.own 1) DFrac.valid_own_one).trans
    (BIUpdate.mono (exists_elim fun _ => sep_elim_left)))
-- `Iris.saved_anything_alloc_cofinite` idx 7: necessary (dq = own (1+1) invalid)
theorem s_any_cof : ¬ drop0% Iris.saved_anything_alloc_cofinite 7 := fun h =>
  bupd_false_unsound ((h (GF := GX SPF) (F := LaterOF IdOF) (Later.next iprop(True)) [] (.own (1 + 1))).trans
    (BIUpdate.mono (exists_elim fun γ => sep_elim_right.trans ((saved_anything_valid γ _ _).trans (pure_mono dq2)))))
-- `Iris.saved_anything_alloc` idx 6: necessary (dq = own (1+1) invalid)
theorem s_any_alloc : ¬ drop0% Iris.saved_anything_alloc 6 := fun h =>
  bupd_false_unsound ((h (GF := GX SPF) (F := LaterOF IdOF) (Later.next iprop(True)) (.own (1 + 1))).trans
    (BIUpdate.mono (exists_elim fun γ => (saved_anything_valid γ _ _).trans (pure_mono dq2))))
-- `Iris.saved_prop_alloc_strong` idx 5: necessary (dq = own (1+1) invalid, I = True)
theorem s_prop_strong5 : ¬ drop0% Iris.saved_prop_alloc_strong 5 := fun h =>
  bupd_false_unsound ((h (GF := GX SPF) (fun _ => True) iprop(True) (.own (1 + 1)) PredInfinite.true).trans
    (BIUpdate.mono (exists_elim fun γ => sep_elim_right.trans ((saved_prop_valid γ _ _).trans (pure_mono dq2)))))
-- `Iris.saved_prop_alloc_strong` idx 6: necessary (I = False)
theorem s_prop_strong6 : ¬ drop0% Iris.saved_prop_alloc_strong 6 := fun h =>
  bupd_false_unsound ((h (GF := GX SPF) (fun _ => False) iprop(True) (.own 1) DFrac.valid_own_one).trans
    (BIUpdate.mono (exists_elim fun _ => sep_elim_left)))
-- `Iris.saved_prop_alloc_cofinite` idx 5: necessary (dq = own (1+1) invalid)
theorem s_prop_cof : ¬ drop0% Iris.saved_prop_alloc_cofinite 5 := fun h =>
  bupd_false_unsound ((h (GF := GX SPF) [] iprop(True) (.own (1 + 1))).trans
    (BIUpdate.mono (exists_elim fun γ => sep_elim_right.trans ((saved_prop_valid γ _ _).trans (pure_mono dq2)))))
-- `Iris.saved_prop_alloc` idx 4: necessary (dq = own (1+1) invalid)
theorem s_prop_alloc : ¬ drop0% Iris.saved_prop_alloc 4 := fun h =>
  bupd_false_unsound ((h (GF := GX SPF) iprop(True) (.own (1 + 1))).trans
    (BIUpdate.mono (exists_elim fun γ => (saved_prop_valid γ _ _).trans (pure_mono dq2))))
-- `Iris.saved_pred_alloc_strong` idx 6: necessary (dq = own (1+1) invalid, I = True)
theorem s_pred_strong6 : ¬ drop0% Iris.saved_pred_alloc_strong 6 := fun h =>
  bupd_false_unsound ((h (GF := GX SDF) (A := Unit) (fun _ => True) (fun _ => iprop(True)) (.own (1 + 1)) PredInfinite.true).trans
    (BIUpdate.mono (exists_elim fun γ => sep_elim_right.trans ((saved_pred_valid γ _ _).trans (pure_mono dq2)))))
-- `Iris.saved_pred_alloc_strong` idx 7: necessary (I = False)
theorem s_pred_strong7 : ¬ drop0% Iris.saved_pred_alloc_strong 7 := fun h =>
  bupd_false_unsound ((h (GF := GX SDF) (A := Unit) (fun _ => False) (fun _ => iprop(True)) (.own 1) DFrac.valid_own_one).trans
    (BIUpdate.mono (exists_elim fun _ => sep_elim_left)))
-- `Iris.saved_pred_alloc_cofinite` idx 6: necessary (dq = own (1+1) invalid)
theorem s_pred_cof : ¬ drop0% Iris.saved_pred_alloc_cofinite 6 := fun h =>
  bupd_false_unsound ((h (GF := GX SDF) (A := Unit) [] (fun _ => iprop(True)) (.own (1 + 1))).trans
    (BIUpdate.mono (exists_elim fun γ => sep_elim_right.trans ((saved_pred_valid γ _ _).trans (pure_mono dq2)))))
-- `Iris.saved_pred_alloc` idx 5: necessary (dq = own (1+1) invalid)
theorem s_pred_alloc : ¬ drop0% Iris.saved_pred_alloc 5 := fun h =>
  bupd_false_unsound ((h (GF := GX SDF) (A := Unit) (fun _ => iprop(True)) (.own (1 + 1))).trans
    (BIUpdate.mono (exists_elim fun γ => (saved_pred_valid γ _ _).trans (pure_mono dq2))))
-- `Iris.ghost_var_alloc_strong` idx 5: necessary (P = False)
theorem g_var_strong : ¬ drop0% Iris.ghost_var_alloc_strong 5 := fun h =>
  bupd_false_unsound ((h (GF := GX (GhostVarF Bool)) true (fun _ => False)).trans
    (BIUpdate.mono (exists_elim fun _ => sep_elim_left)))
-- `Iris.ghost_map_alloc_strong` idx 9: necessary (P = False)
theorem g_map_strong : ¬ drop0% Iris.ghost_map_alloc_strong 9 := fun h =>
  bupd_false_unsound ((h (GF := GX GMF) (K := Nat) (V := Bool) (H := TM) (fun _ => False) ∅).trans
    (BIUpdate.mono (exists_elim fun _ => sep_elim_left)))
-- `Iris.ghost_map_alloc_strong_empty` idx 8: necessary (P = False)
theorem g_map_strong_empty : ¬ drop0% Iris.ghost_map_alloc_strong_empty 8 := fun h =>
  bupd_false_unsound ((h (GF := GX GMF) (K := Nat) (V := Bool) (H := TM) (fun _ => False)).trans
    (BIUpdate.mono (exists_elim fun _ => sep_elim_left)))

-- `Iris.ghost_var_update_2` idx 9: necessary (q1 = q2 = 1/4 with a 1/2 piece kept: update to false, agreement with the kept piece (true))
theorem g_var_upd2 : ¬ drop0% Iris.ghost_var_update_2 9 := fun h =>
  bupd_false_unsound (GF := GX (GhostVarF Bool)) (by
    iintro
    imod ghost_var_alloc (GF := GX (GhostVarF Bool)) true with ⟨%γ, H⟩
    ieval (rewrite [← Qp.half_add_half 1]) at H
    ihave ⟨H1, H2⟩ := ghost_var_split γ true (Qp.half 1) (Qp.half 1) $$ H
    ieval (rewrite [← Qp.half_add_half (Qp.half 1)]) at H1
    ihave ⟨Ha, Hb⟩ := ghost_var_split γ true _ _ $$ H1
    imod h false γ true _ true _ $$ Ha Hb with ⟨Ha, _⟩
    ihave %He := ghost_var_agree γ false _ true _ $$ Ha H2
    exact absurd He (by decide))

-- `Iris.instFrameIPropGhost_varOwnOfFrameFractionalQp` idx 9: necessary (q1 = q = 1/4, q2 = 1: frame yields full ownership while a 1/2 piece remains; update and agreement)
theorem g_var_frame : ¬ drop0% Iris.instFrameIPropGhost_varOwnOfFrameFractionalQp 9 := fun h =>
  bupd_false_unsound (GF := GX (GhostVarF Bool)) (by
    iintro
    imod ghost_var_alloc (GF := GX (GhostVarF Bool)) true with ⟨%γ, H⟩
    ieval (rewrite [← Qp.half_add_half 1]) at H
    ihave ⟨H1, H2⟩ := ghost_var_split γ true (Qp.half 1) (Qp.half 1) $$ H
    ieval (rewrite [← Qp.half_add_half (Qp.half 1)]) at H1
    ihave ⟨Ha, Hb⟩ := ghost_var_split γ true _ _ $$ H1
    ihave Hc := (h false γ true (Qp.half (Qp.half 1)) 1 (Qp.half (Qp.half 1))).frame $$ [Ha Hb]
    · isplitl [Ha]
      · iexact Ha
      · iexact Hb
    imod ghost_var_update false γ true $$ Hc with Hc
    ihave %He := ghost_var_agree γ false _ true _ $$ Hc H2
    exact absurd He (by decide))

-- `Iris.instCombineSepAsIPropGhost_varOfIsOpDFracMerge` idx 9: necessary (dq1 = dq2 = 1/4, dq = 1: full ownership while a 1/2 piece remains; update and agreement)
theorem g_var_combine : ¬ drop0% Iris.instCombineSepAsIPropGhost_varOfIsOpDFracMerge 9 := fun h =>
  bupd_false_unsound (GF := GX (GhostVarF Bool)) (by
    iintro
    imod ghost_var_alloc (GF := GX (GhostVarF Bool)) true with ⟨%γ, H⟩
    ieval (rewrite [← Qp.half_add_half 1]) at H
    ihave ⟨H1, H2⟩ := ghost_var_split γ true (Qp.half 1) (Qp.half 1) $$ H
    ieval (rewrite [← Qp.half_add_half (Qp.half 1)]) at H1
    ihave ⟨Ha, Hb⟩ := ghost_var_split γ true _ _ $$ H1
    ihave Hc := (h γ true (.own (Qp.half (Qp.half 1))) true (.own (Qp.half (Qp.half 1))) (.own 1)).combine_sep_as $$ [Ha Hb]
    · isplitl [Ha]
      · iexact Ha
      · iexact Hb
    imod ghost_var_update false γ true $$ Hc with Hc
    ihave %He := ghost_var_agree γ false _ true _ $$ Hc H2
    exact absurd He (by decide))

-- `Iris.saved_prop_update_2` idx 8: necessary (q1 = q2 = 1/4 with a 1/2 piece kept: update to False, agreement gives ▷ (False ≡ True))
theorem s_prop_upd2 : ¬ drop0% Iris.saved_prop_update_2 8 := fun h =>
  bupd_later_false (GF := GX SPF) (by
    iintro
    imod saved_prop_alloc (GF := GX SPF) iprop(⌜True⌝) (.own 1) DFrac.valid_own_one with ⟨%γ, H⟩
    ieval (rewrite [← Qp.half_add_half 1]) at H
    ihave ⟨H1, H2⟩ := (saved_prop_fractional γ iprop(⌜True⌝)).fractional (Qp.half 1) (Qp.half 1) |>.mp $$ H
    ieval (rewrite [← Qp.half_add_half (Qp.half 1)]) at H1
    ihave ⟨Ha, Hb⟩ := (saved_prop_fractional γ iprop(⌜True⌝)).fractional _ _ |>.mp $$ H1
    imod h iprop(⌜False⌝) γ _ _ iprop(⌜True⌝) iprop(⌜True⌝) $$ [Ha Hb] with ⟨Ha, _⟩
    · isplitl [Ha]
      · iexact Ha
      · iexact Hb
    imodintro
    iapply eq_ft_false
    iapply saved_prop_agree
    isplitl [Ha]
    · iexact Ha
    · iexact H2)

-- `Iris.saved_anything_update_2` idx 10: necessary (F = Later Id, as saved_prop_update_2)
theorem s_any_upd2 : ¬ drop0% Iris.saved_anything_update_2 10 := fun h =>
  have h' : ∀ γ q1 q2 (P1 P2 Q : IProp (GX SPF)), saved_prop_own γ (.own q1) P1 ∗ saved_prop_own γ (.own q2) P2 ⊢
      |==> (saved_prop_own γ (.own q1) Q ∗ saved_prop_own γ (.own q2) Q) :=
    fun γ q1 q2 P1 P2 Q => h (F := LaterOF IdOF) (Later.next Q) γ q1 q2 (Later.next P1) (Later.next P2)
  bupd_later_false (GF := GX SPF) (by
    iintro
    imod saved_prop_alloc (GF := GX SPF) iprop(⌜True⌝) (.own 1) DFrac.valid_own_one with ⟨%γ, H⟩
    ieval (rewrite [← Qp.half_add_half 1]) at H
    ihave ⟨H1, H2⟩ := (saved_prop_fractional γ iprop(⌜True⌝)).fractional (Qp.half 1) (Qp.half 1) |>.mp $$ H
    ieval (rewrite [← Qp.half_add_half (Qp.half 1)]) at H1
    ihave ⟨Ha, Hb⟩ := (saved_prop_fractional γ iprop(⌜True⌝)).fractional _ _ |>.mp $$ H1
    imod h' γ (Qp.half (Qp.half 1)) (Qp.half (Qp.half 1)) iprop(⌜True⌝) iprop(⌜True⌝) iprop(⌜False⌝) $$ [Ha Hb] with ⟨Ha, _⟩
    · isplitl [Ha]
      · iexact Ha
      · iexact Hb
    imodintro
    iapply eq_ft_false
    iapply saved_prop_agree
    isplitl [Ha]
    · iexact Ha
    · iexact H2)

-- `Iris.saved_pred_update_2` idx 9: necessary (A = Unit, as saved_prop_update_2)
theorem s_pred_upd2 : ¬ drop0% Iris.saved_pred_update_2 9 := fun h =>
  bupd_later_false (GF := GX SDF) (by
    iintro
    imod saved_pred_alloc (GF := GX SDF) (A := Unit) (fun _ => iprop(⌜True⌝)) (.own 1) DFrac.valid_own_one with ⟨%γ, H⟩
    ieval (rewrite [← Qp.half_add_half 1]) at H
    ihave ⟨H1, H2⟩ := (saved_pred_fractional γ (fun _ : Unit => iprop(⌜True⌝))).fractional (Qp.half 1) (Qp.half 1) |>.mp $$ H
    ieval (rewrite [← Qp.half_add_half (Qp.half 1)]) at H1
    ihave ⟨Ha, Hb⟩ := (saved_pred_fractional γ (fun _ : Unit => iprop(⌜True⌝))).fractional _ _ |>.mp $$ H1
    imod h (fun _ => iprop(⌜False⌝)) γ _ _ (fun _ => iprop(⌜True⌝)) (fun _ => iprop(⌜True⌝)) $$ [Ha Hb] with ⟨Ha, _⟩
    · isplitl [Ha]
      · iexact Ha
      · iexact Hb
    imodintro
    iapply eq_ft_false
    iapply saved_pred_agree γ _ _ (fun _ => iprop(⌜False⌝)) (fun _ => iprop(⌜True⌝)) ()
    isplitl [Ha]
    · iexact Ha
    · iexact H2)

open BigSepM in
-- `Iris.ghost_map_insert` idx 10: necessary (GX with a ghost map Nat ↦ Bool: insert key 0 twice (true, then false): fragments 0 ↦ true and 0 ↦ false disagree)
theorem gm_insert : ¬ drop0% Iris.ghost_map_insert 10 := fun h =>
  bupd_false_unsound (GF := GX GMF) (by
    iintro
    imod ghost_map_alloc_empty (GF := GX GMF) (K := Nat) (V := Bool) (H := TM) with ⟨%γ, Ha⟩
    imod ghost_map_insert (m := (∅ : TM Bool)) 0 true (Iris.Std.LawfulPartialMap.get?_empty 0) $$ Ha with ⟨Ha, H1⟩
    imod h (γ := γ) 0 false $$ Ha with ⟨_, H2⟩
    ihave %He := ghost_map_elem_agree γ 0 _ _ true false $$ [H1 H2]
    · isplitl [H1]
      · iexact H1
      · iexact H2
    exact absurd He (by decide))

-- `Iris.ghost_map_insert_persist` idx 10: necessary (GX with a ghost map Nat ↦ Bool: key 0 ↦ true present, persistent insert of 0 ↦ false: disagreement)
theorem gm_insert_persist : ¬ drop0% Iris.ghost_map_insert_persist 10 := fun h =>
  bupd_false_unsound (GF := GX GMF) (by
    iintro
    imod ghost_map_alloc_empty (GF := GX GMF) (K := Nat) (V := Bool) (H := TM) with ⟨%γ, Ha⟩
    imod ghost_map_insert (m := (∅ : TM Bool)) 0 true (Iris.Std.LawfulPartialMap.get?_empty 0) $$ Ha with ⟨Ha, H1⟩
    imod h (γ := γ) 0 false $$ Ha with ⟨_, H2⟩
    ihave %He := ghost_map_elem_agree γ 0 _ _ true false $$ [H1 H2]
    · isplitl [H1]
      · iexact H1
      · iexact H2
    exact absurd He (by decide))

-- `Iris.ghost_map_insert_big` idx 10: necessary (GX with a ghost map Nat ↦ Bool: m = {0 ↦ true} with its fragment, m' = {0 ↦ false}: disagreement)
theorem gm_insert_big : ¬ drop0% Iris.ghost_map_insert_big 10 := fun h =>
  bupd_false_unsound (GF := GX GMF) (by
    iintro
    imod ghost_map_alloc_empty (GF := GX GMF) (K := Nat) (V := Bool) (H := TM) with ⟨%γ, Ha⟩
    imod ghost_map_insert (m := (∅ : TM Bool)) 0 true (Iris.Std.LawfulPartialMap.get?_empty 0) $$ Ha with ⟨Ha, H1⟩
    imod h (γ := γ) (Iris.Std.PartialMap.singleton 0 false : TM Bool) $$ Ha with ⟨_, Hb⟩
    ihave H2 := BigSepM.bigSepM_singleton.mp $$ Hb
    ihave %He := ghost_map_elem_agree γ 0 _ _ true false $$ [H1 H2]
    · isplitl [H1]
      · iexact H1
      · iexact H2
    exact absurd He (by decide))

-- `Iris.ghost_map_insert_persist_big` idx 10: necessary (GX with a ghost map Nat ↦ Bool: m = {0 ↦ true} with its fragment, m' = {0 ↦ false}: disagreement)
theorem gm_insert_persist_big : ¬ drop0% Iris.ghost_map_insert_persist_big 10 := fun h =>
  bupd_false_unsound (GF := GX GMF) (by
    iintro
    imod ghost_map_alloc_empty (GF := GX GMF) (K := Nat) (V := Bool) (H := TM) with ⟨%γ, Ha⟩
    imod ghost_map_insert (m := (∅ : TM Bool)) 0 true (Iris.Std.LawfulPartialMap.get?_empty 0) $$ Ha with ⟨Ha, H1⟩
    imod h (γ := γ) (Iris.Std.PartialMap.singleton 0 false : TM Bool) $$ Ha with ⟨_, Hb⟩
    ihave H2 := BigSepM.bigSepM_singleton.mp $$ Hb
    ihave %He := ghost_map_elem_agree γ 0 _ _ true false $$ [H1 H2]
    · isplitl [H1]
      · iexact H1
      · iexact H2
    exact absurd He (by decide))

-- `Iris.ghost_map_update_big` idx 11: necessary (GX with a ghost map Nat ↦ Bool: m = {0 ↦ true} with its fragment, m0 = ∅, m1 = {0 ↦ false}: disagreement)
theorem gm_update_big : ¬ drop0% Iris.ghost_map_update_big 11 := fun h =>
  bupd_false_unsound (GF := GX GMF) (by
    iintro
    imod ghost_map_alloc_empty (GF := GX GMF) (K := Nat) (V := Bool) (H := TM) with ⟨%γ, Ha⟩
    imod ghost_map_insert (m := (∅ : TM Bool)) 0 true (Iris.Std.LawfulPartialMap.get?_empty 0) $$ Ha with ⟨Ha, H1⟩
    imod h (γ := γ) (∅ : TM Bool) (Iris.Std.PartialMap.singleton 0 false : TM Bool) $$ Ha [] with ⟨_, Hb⟩
    · iapply BigSepM.bigSepM_empty.mpr
      itrivial
    ihave H2 := BigSepM.bigSepM_singleton.mp $$ Hb
    ihave %He := ghost_map_elem_agree γ 0 _ _ true false $$ [H1 H2]
    · isplitl [H1]
      · iexact H1
      · iexact H2
    exact absurd He (by decide))

/-- View shifts as persistent implications. -/
def vsI (_ _ : CoPset) (P Q : UPred AF) : UPred AF := iprop(□ (P → Q))
theorem vsI_trans (E1 E2 E3 : CoPset) (P Q R : UPred AF) : vsI E1 E2 P Q ∧ vsI E2 E3 Q R ⊢ vsI E1 E3 P R := by
  unfold vsI
  iintro ⟨#H1, #H2⟩
  imodintro
  iintro HP
  iapply H2
  iapply H1
  iexact HP
theorem af_not_a2 : ¬ (⊢ (UPred.ownM AF.a : UPred AF)) := fun h => by
  rcases h 0 ⟨.e, trivial⟩ (.inl rfl) with h1 | h1 <;> cases h1
theorem iprop_true_ne_false : (iprop(True) : UPred AF) ≠ iprop(False) := fun e =>
  (congrArg (fun P : UPred AF => P.holds 0 ⟨AF.e, trivial⟩) e).mp trivial

-- `Iris.fupd_vs_intro` idx 5: necessary (UPred AF, vs = False, P = True)
theorem v_intro : ¬ drop0% Iris.fupd_vs_intro 5 := fun h =>
  UPred.consistency (M := AF) ((true_intro.trans (h (fun _ _ _ _ => iprop(False)) ∅ iprop(True))).trans
    (exists_elim fun _ => sep_elim_right))

theorem vsI_true : ⊢ fupd_vs vsI ∅ ∅ (iprop(True) : UPred AF) := by
  unfold vsI
  iexists iprop(True)
  isplitl []
  · ipureintro; trivial
  · imodintro
    iintro _
    ipureintro; trivial
theorem vsI_false : fupd_vs vsI ∅ ∅ (iprop(False) : UPred AF) ⊢ iprop(False) := by
  unfold vsI
  iintro ⟨%R, HR, #H⟩
  iapply H
  iexact HR

-- `Iris.fupd_vs_mono` idx 8: necessary (UPred AF, vs E1 E2 P Q = □ (P → Q) (transitive, implied by □ (P → Q)), P = True, Q = False)
theorem v_mono8 : ¬ drop0% Iris.fupd_vs_mono 8 := fun h =>
  UPred.consistency (M := AF) ((vsI_true.trans
    (h vsI (E1 := ∅) (E2 := ∅) (P := iprop(True)) (Q := iprop(False)) vsI_trans (fun _ _ _ => .rfl))).trans vsI_false)

-- `Iris.fupd_vs_mono` idx 10: necessary (UPred AF, vs _ _ _ Q = ⌜Q = False⌝ (transitive), P = False ⊢ Q = True; True ≠ False as UPreds)
theorem v_mono10 : ¬ drop0% Iris.fupd_vs_mono 10 := fun h => by
  have H := h (M := AF) (fun _ _ _ Q => iprop(⌜Q = iprop(False)⌝)) (E1 := ∅) (E2 := ∅) (P := iprop(False)) (Q := iprop(True))
    false_elim (fun _ _ _ _ _ _ => and_elim_r)
  have L : ⊢ fupd_vs (M := AF) (fun _ _ _ Q => iprop(⌜Q = iprop(False)⌝)) ∅ ∅ iprop(False) := by
    iexists iprop(True)
    isplitl []
    · ipureintro; trivial
    · ipureintro; rfl
  exact iprop_true_ne_false (UPred.pure_soundness (M := AF) ((L.trans H).trans (exists_elim fun _ => sep_elim_right)))

-- `Iris.fupd_vs_mask_frame_r` idx 8: necessary (UPred AF, vs E1 _ _ _ = ⌜E1 ## ⊤⌝, E1 = E2 = ∅, Ef = ⊤)
theorem v_mask8 : ¬ drop0% Iris.fupd_vs_mask_frame_r 8 := fun h => by
  have L : ⊢ fupd_vs (M := AF) (fun E1 _ _ _ => iprop(⌜E1 ## ⊤⌝)) ∅ ∅ iprop(True) := by
    iexists iprop(True)
    isplitl []
    · ipureintro; trivial
    · ipureintro; exact fun _ ⟨h1, _⟩ => CoPset.mem_empty h1
  exact full_not_disj (UPred.pure_soundness (M := AF) ((L.trans
    (h (fun E1 _ _ _ => iprop(⌜E1 ## ⊤⌝)) (E1 := ∅) (E2 := ∅) (Ef := ⊤) (P := iprop(True)) (fun _ ⟨h1, _⟩ => CoPset.mem_empty h1))).trans
      (exists_elim fun _ => sep_elim_right)))

-- `Iris.fupd_vs_mask_frame_r` idx 7: necessary (UPred AF, vs E1 E2 = ⌜1 ∈ E1 ∧ 1 ∉ E2⌝ (preserved by disjoint framing), E1 = Ef = ⊤, E2 = ∅)
theorem v_mask7 : ¬ drop0% Iris.fupd_vs_mask_frame_r 7 := fun h => by
  let vsX : CoPset → CoPset → UPred AF → UPred AF → UPred AF := fun E1 E2 _ _ => iprop(⌜Pos.xH ∈ E1 ∧ Pos.xH ∉ E2⌝)
  have L : ⊢ fupd_vs vsX ⊤ ∅ iprop(True) := by
    iexists iprop(True)
    isplitl []
    · ipureintro; trivial
    · ipureintro; exact ⟨CoPset.mem_full, CoPset.mem_empty⟩
  have H := h vsX (E1 := ⊤) (E2 := ∅) (Ef := ⊤) (P := iprop(True)) (fun E1 E2 Ef _ _ HE => pure_mono fun ⟨h1, h2⟩ =>
    ⟨Iris.Std.LawfulSet.mem_union.mpr (.inl h1), fun hm => (Iris.Std.LawfulSet.mem_union.mp hm).elim h2 (fun hf => HE .xH ⟨h1, hf⟩)⟩)
  exact (UPred.pure_soundness (M := AF) ((L.trans H).trans (exists_elim fun _ => sep_elim_right))).2 CoPset.mem_full

-- `Iris.fupd_vs_frame_r` idx 7: necessary (UPred AF, vs _ _ _ Q = ⌜⊢ Q⌝, P = True, Q = ownM a (not valid))
theorem v_frame : ¬ drop0% Iris.fupd_vs_frame_r 7 := fun h => by
  let vsV : CoPset → CoPset → UPred AF → UPred AF → UPred AF := fun _ _ _ Q => iprop(⌜⊢ Q⌝)
  have L : (UPred.ownM AF.a : UPred AF) ⊢ fupd_vs vsV ∅ ∅ iprop(True) ∗ UPred.ownM AF.a := by
    iintro H
    isplitr [H]
    · iexists iprop(True)
      isplitl []
      · ipureintro; trivial
      · ipureintro; exact true_intro
    · iexact H
  have H := (L.trans (h vsV (E1 := ∅) (E2 := ∅) (P := iprop(True)) (Q := UPred.ownM AF.a))).trans
    (exists_elim fun _ => sep_elim_right)
  exact af_not_a2 ((H 0 ⟨.a, trivial⟩ (.inr rfl)).trans sep_elim_right)


noncomputable abbrev TRF : COFE.OFunctorPre := Iris.constOF Iris.Algebra.TimeReceipt
instance trGX : TimeReceiptGpreS (GX TRF) := ⟨gxElem TRF⟩

-- `Iris.TimeReceipt.excl_weaken` idx 4: necessary (GX with TimeReceipt slot, supply 0 allocated: ⧖+ 0 gives ⧖+ 1, supply_bound_both gives 1 ≤ 0)
theorem tr_excl : ¬ drop0% Iris.TimeReceipt.excl_weaken 4 := fun h =>
  bupd_false_unsound (GF := GX TRF) (by
    iintro
    imod TimeReceipt.supply_alloc (GF := GX TRF) 0 with ⟨%TR, Hs, He⟩
    imod TimeReceipt.pers_zero (TR := TR) with Hp
    ihave He := h (TR := TR) (n₁ := 0) 1 $$ He
    ihave %Hb := TimeReceipt.supply_bound_both 1 0 0 $$ Hs He Hp
    exact absurd Hb (by decide))

-- `Iris.TimeReceipt.pers_weaken` idx 4: necessary (supply 0 allocated: ⧖□ 0 gives ⧖□ 1, supply_pers_bound gives 1 ≤ 0)
theorem tr_pers : ¬ drop0% Iris.TimeReceipt.pers_weaken 4 := fun h =>
  bupd_false_unsound (GF := GX TRF) (by
    iintro
    imod TimeReceipt.supply_alloc (GF := GX TRF) 0 with ⟨%TR, Hs, _⟩
    imod TimeReceipt.pers_zero (TR := TR) with Hp
    ihave Hp := h (TR := TR) (n₁ := 0) 1 $$ Hp
    ihave %Hb := TimeReceipt.supply_pers_bound 1 0 $$ Hs Hp
    exact absurd Hb (by decide))

namespace W7c0
open Iris Iris.Std
attribute [local instance] lexOrd
/-- Finite sets of pairs of naturals (W2c4). -/
abbrev PS := Std.ExtTreeSet (Nat × Nat) compare
theorem ps_mem {p q : Nat × Nat} : p ∈ ({q} : PS) ↔ p = q := Std.LawfulSet.mem_singleton
theorem ps_mem_u {p : Nat × Nat} {L1 L2 : PS} : p ∈ L1 ∪ L2 ↔ p ∈ L1 ∨ p ∈ L2 := Std.LawfulSet.mem_union
theorem bij_sg (a b : Nat) : SetBijective ({(a, b)} : PS) := fun hab => by
  rw [ps_mem] at hab
  cases hab
  exact ⟨fun b' hb' => by rw [ps_mem] at hb'; cases hb'; rfl,
         fun a' ha' => by rw [ps_mem] at ha'; cases ha'; rfl⟩
theorem bij_bad1 {L : PS} {a b c : Nat} (h1 : (a, b) ∈ L) (h2 : (a, c) ∈ L) (hne : b ≠ c) :
    ¬ SetBijective L := fun h => hne ((h h2).1 b h1)
theorem bij_bad2 {L : PS} {a b c : Nat} (h1 : (a, c) ∈ L) (h2 : (b, c) ∈ L) (hne : a ≠ b) :
    ¬ SetBijective L := fun h => hne ((h h2).2 a h1)
noncomputable abbrev SBF : COFE.OFunctorPre := constOF (SetBij PS)
instance sbGX : SetBijG (GX SBF) Nat Nat PS := ⟨gxElem SBF⟩
end W7c0
open W7c0 Iris Iris.BI
section SB
attribute [local instance] lexOrd

-- `Iris.set_bij_own_elem_get` idx 11: necessary (S = ExtTreeSet (Nat × Nat), auth ∅ gives elem 0 0, set_bij_elem_of gives (0,0) ∈ ∅)
theorem b_get : ¬ drop0% Iris.set_bij_own_elem_get 11 := fun h =>
  bupd_false_unsound (GF := GX SBF) (by
    iintro
    imod set_bij_own_alloc_empty (GF := GX SBF) (S := PS) with ⟨%γ, H⟩
    ihave ⟨H, #H2⟩ := persistent_entails_left (h (γ := γ) (dq := .own 1) (L := (∅ : PS)) 0 0) $$ H
    ihave %Hm := set_bij_elem_of 0 0 $$ [H H2]
    · isplitl [H]
      · iexact H
      · iexact H2
    exact (Std.LawfulSet.mem_empty Hm).elim)

-- `Iris.set_bij_own_alloc` idx 7: necessary (L = {(0,0), (0,1)} not bijective; the allocated auth is valid only for bijective L)
theorem b_alloc : ¬ drop0% Iris.set_bij_own_alloc 7 := fun h =>
  bupd_false_unsound (GF := GX SBF) (by
    iintro
    imod h (GF := GX SBF) (({(0, 0)} : PS) ∪ {(0, 1)}) with ⟨%γ, H, _⟩
    ihave %Hv := set_bij_own_valid $$ H
    exact (bij_bad1 (ps_mem_u.mpr (.inl (ps_mem.mpr rfl))) (ps_mem_u.mpr (.inr (ps_mem.mpr rfl))) (by decide) Hv.2).elim)

-- `Iris.set_bij_own_extend` idx 10: necessary (L = {(0,0)}, (a, b) = (0, 1): result {(0,1),(0,0)} not bijective)
theorem b_ext10 : ¬ drop0% Iris.set_bij_own_extend 10 := fun h =>
  bupd_false_unsound (GF := GX SBF) (by
    iintro
    imod set_bij_own_alloc (GF := GX SBF) ({(0, 0)} : PS) (bij_sg 0 0) with ⟨%γ, H, _⟩
    imod h (γ := γ) (L := ({(0, 0)} : PS)) 0 1 (fun a' hm => by rw [ps_mem] at hm; cases hm) $$ H with ⟨H, _⟩
    ihave %Hv := set_bij_own_valid $$ H
    exact (bij_bad1 (ps_mem_u.mpr (.inr (ps_mem.mpr rfl))) (ps_mem_u.mpr (.inl (ps_mem.mpr rfl))) (by decide) Hv.2).elim)

-- `Iris.set_bij_own_extend` idx 11: necessary (L = {(0,0)}, (a, b) = (1, 0): result {(1,0),(0,0)} not bijective)
theorem b_ext11 : ¬ drop0% Iris.set_bij_own_extend 11 := fun h =>
  bupd_false_unsound (GF := GX SBF) (by
    iintro
    imod set_bij_own_alloc (GF := GX SBF) ({(0, 0)} : PS) (bij_sg 0 0) with ⟨%γ, H, _⟩
    imod h (γ := γ) (L := ({(0, 0)} : PS)) 1 0 (fun b' hm => by rw [ps_mem] at hm; cases hm) $$ H with ⟨H, _⟩
    ihave %Hv := set_bij_own_valid $$ H
    exact (bij_bad2 (ps_mem_u.mpr (.inr (ps_mem.mpr rfl))) (ps_mem_u.mpr (.inl (ps_mem.mpr rfl))) (by decide) Hv.2).elim)

-- `_private.Iris.Instances.Lib.SetBij.0.Iris.cmraValid_op_pure` idx 10: necessary (φ = False, a₁ = a₂ = unit (owned by iOwn_unit))
theorem b_valid_op : ¬ drop0% _private.Iris.Instances.Lib.SetBij.«0».Iris.cmraValid_op_pure 10 := fun h =>
  bupd_false_unsound (GF := GX SBF) (by
    iintro
    imod iOwn_unit (E := (SetBijG.elem : ElemG (GX SBF) SBF)) (γ := 0) (ε := UORA.unit) with H1
    imod iOwn_unit (E := (SetBijG.elem : ElemG (GX SBF) SBF)) (γ := 0) (ε := UORA.unit) with H2
    imodintro
    iapply h (GF := GX SBF) (A := Nat) (B := Nat) (S := PS) (γ := 0) (a₁ := UORA.unit) (a₂ := UORA.unit) (φ := False)
    isplitl [H1]
    · iexact H1
    · iexact H2)
end SB

theorem laterF_ne_true : (iprop(▷ False) : UPred AF) ≠ iprop(True) := fun e =>
  (congrArg (fun P : UPred AF => P.holds 1 ⟨AF.e, trivial⟩) e).mpr trivial
theorem laterF_ne_false : (iprop(▷ False) : UPred AF) ≠ iprop(False) := fun e =>
  (congrArg (fun P : UPred AF => P.holds 0 ⟨AF.e, trivial⟩) e).mp trivial

-- `Iris.fupd_vs_ne` idx 5: necessary (UPred AF, vs _ _ _ Q = ⌜Q = True⌝ (not NE): True and ▷ False are 0-close but differ)
theorem v_ne : ¬ drop0% Iris.fupd_vs_ne 5 := fun h => by
  let vsT : CoPset → CoPset → UPred AF → UPred AF → UPred AF := fun _ _ _ Q => iprop(⌜Q = iprop(True)⌝)
  have L : ⊢ fupd_vs vsT ∅ ∅ iprop(True) := by
    iexists iprop(True)
    isplitl []
    · ipureintro; trivial
    · ipureintro; rfl
  have hd : (iprop(True) : UPred AF) ≡{0}≡ iprop(▷ False) := fun n' x hn p => by
    obtain rfl : n' = 0 := by omega
    exact ⟨fun _ => trivial, fun _ => trivial⟩
  have H := ((h vsT ∅ ∅).ne hd) 0 AF.e (Nat.le_refl _) trivial
  have H2 := H.mp (L 0 ⟨AF.e, trivial⟩ (.inl rfl))
  exact laterF_ne_true ((exists_elim (Φ := fun R => iprop(R ∗ vsT ∅ ∅ R iprop(▷ False))) fun _ => sep_elim_right) 0 ⟨AF.e, trivial⟩ H2)

-- `Iris.fupd_vs_mono` idx 9: necessary (UPred AF, vs P Q = □ (P → Q) ∨ ⌜Q = False⌝ (not transitive), P = False ⊢ Q = ▷ False; at step 1)
theorem v_mono9 : ¬ drop0% Iris.fupd_vs_mono 9 := fun h => by
  let vsO : CoPset → CoPset → UPred AF → UPred AF → UPred AF := fun _ _ P Q => iprop(□ (P → Q) ∨ ⌜Q = iprop(False)⌝)
  have L : ⊢ fupd_vs vsO ∅ ∅ iprop(False) := by
    iexists iprop(True)
    isplitl []
    · ipureintro; trivial
    · iright; ipureintro; rfl
  have H := h vsO (E1 := ∅) (E2 := ∅) (P := iprop(False)) (Q := iprop(▷ False)) false_elim (fun _ _ _ => or_intro_l)
  have R : fupd_vs vsO ∅ ∅ iprop(▷ False) ⊢ iprop(▷ False ∨ ⌜(iprop(▷ False) : UPred AF) = iprop(False)⌝) := by
    iintro ⟨%R, HR, (#H | %He)⟩
    · ileft
      iapply H
      iexact HR
    · iright
      ipureintro
      exact He
  rcases ((L.trans H).trans R) 1 ⟨AF.e, trivial⟩ (.inl rfl) with h1 | h1
  · exact h1
  · exact laterF_ne_false h1

-- `Iris.inv_acc_timeless` idx 6: necessary (P = <pers> (|={⊤,⊤∖N}=> False), not timeless: allocating inv N P and opening it gives ▷ P ⊢ P, Löb gives ⊢ P, fupd_soundness)
theorem i_timeless6 : ¬ drop0% Iris.inv_acc_timeless 6 := fun h =>
  fupd_later_false (GF := GX TokenF) (⊤ \ ↑nroot) fun {_} => by
    have HL : (iprop(▷ <pers> (|={⊤, ⊤ \ ↑nroot}=> ⌜False⌝)) : IProp (GX TokenF)) ⊢
        iprop(<pers> (|={⊤, ⊤ \ ↑nroot}=> ⌜False⌝)) := by
      iintro #HQ
      imodintro
      imod inv_alloc nroot ⊤ iprop(<pers> (|={⊤, ⊤ \ ↑nroot}=> ⌜False⌝)) $$ HQ with #Hinv
      imod h (E := ⊤) (N := nroot) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨#HQ', Hcl⟩
      imod Hcl $$ HQ'
      ihave HF := persistently_elim $$ HQ'
      iexact HF
    have H2 : ⊢ (iprop(<pers> (|={⊤, ⊤ \ ↑nroot}=> ⌜False⌝)) : IProp (GX TokenF)) := true_intro.trans (loeb_weak HL)
    exact (H2.trans persistently_elim).trans (BIFUpdate.mono later_intro)

theorem na_unfold {hlc : HasLC} [InvGS_gen hlc (GX NaInvF)] {p : NaInvPoolName} {N : Namespace} {P : IProp (GX NaInvF)} :
    NonAtomicInvariant.inv p N P ⊢ iprop(∃ i, ⌜i ∈ (↑N : CoPset)⌝ ∧
      Iris.inv N iprop(P ∗ iOwn (E := NaInvG.inv) p (.valid ∅, .valid {i}) ∨ NonAtomicInvariant.own p {i})) := .rfl

-- `Iris.NonAtomicInvariant.inv_acc` idx 9: necessary (unfold the na-invariant, open its atomic invariant at ⊤, then the dropped lemma at E = ⊤ ∖ N gives a second copy of the exclusive resource (or the stored pool token clashes with own p ⊤))
theorem n_inv_acc9 : ¬ drop0% Iris.NonAtomicInvariant.inv_acc 9 := fun h =>
  fupd_later_false (GF := GX NaInvF) (⊤ \ ↑nroot) fun {_} => by
    iintro
    imod own_full_alloc (F := NaInvF) with ⟨%γ0, Ho⟩
    imod NonAtomicInvariant.alloc with ⟨%p, Hp⟩
    imod NonAtomicInvariant.inv_alloc (p := p) (E := ⊤) (N := nroot) (P := own1 NaInvF γ0) $$ [Ho] with #Hinv
    · inext; iexact Ho
    ihave H3 := na_unfold $$ Hinv
    icases H3 with ⟨%i, %Hi, #Hat⟩
    imod inv_acc (E := ⊤) (N := nroot) (fun _ _ => CoPset.mem_full) $$ Hat with ⟨Hc, _⟩
    icases Hc with (⟨H2, _⟩ | Hi2)
    · imod h (E := ⊤ \ ↑nroot) (F := ⊤) (N := nroot) (fun _ _ => CoPset.mem_full) $$ Hinv Hp with ⟨H1, _, _⟩
      imodintro
      iapply dup_later_false γ0
      isplitl [H1]
      · iexact H1
      · iexact H2
    · imodintro
      inext
      ihave %Hd := NonAtomicInvariant.own_disjoint $$ Hi2 Hp
      exact (Hd i ⟨Iris.Std.LawfulSet.mem_singleton.mpr rfl, CoPset.mem_full⟩).elim

instance boxGX : BoxG (GF := GX BoxF) := ⟨⟩
theorem laterIf_false_elim {PROP : Type _} [BI PROP] {P : PROP} : iprop(▷?false P) ⊢ P := .rfl

-- `Iris.slice_empty` idx 14: necessary (GX with the box functor; box B1 = {γ ↦ true} holding the exclusive resource Q via slice_insert_full; the dropped lemma on a fresh empty box yields ▷ Q, real slice_empty on B1 a second ▷ Q)
theorem bx_empty14 : ¬ drop0% Iris.slice_empty 14 := fun h =>
  fupd_later_false (GF := GX BoxF) ⊤ fun {_} => by
    iintro
    imod own_full_alloc (F := BoxF) with ⟨%γ0, Ho⟩
    ihave Hb := box_alloc (GF := GX BoxF) (M := TM) nroot
    ihave Hb2 := box_alloc (GF := GX BoxF) (M := TM) nroot
    imod slice_insert_full (E := ⊤) (q := false) (f := (∅ : TM Bool)) (P := iprop(emp)) (Q := own1 BoxF γ0) (N := nroot)
      (fun _ _ => CoPset.mem_full) $$ [Ho Hb] with ⟨%γ, %Hγ, #Hs, Hb⟩
    · isplitl [Ho]
      · inext; iexact Ho
      · iexact Hb
    imod h (E := ⊤) (q := false) (f := (∅ : TM Bool)) (P := iprop(emp)) (Q := own1 BoxF γ0) (γ := γ) (N := nroot)
      (fun _ _ => CoPset.mem_full) $$ [Hb2] with ⟨H1, _⟩
    · isplitl []
      · iexact Hs
      · iexact Hb2
    imod slice_empty (E := ⊤) (q := false) (P := iprop(own1 BoxF γ0 ∗ emp)) (N := nroot) (fun _ _ => CoPset.mem_full)
      (Iris.Std.LawfulPartialMap.get?_insert_eq rfl) $$ [Hb] with ⟨H2, _⟩
    · isplitl []
      · iexact Hs
      · iexact Hb
    imodintro
    iapply dup_later_false γ0
    isplitl [H1]
    · iexact H1
    · iexact H2

-- `Iris.slice_delete_full` idx 14: necessary (GX with the box functor; box B1 = {γ ↦ true} holding the exclusive resource Q via slice_insert_full; the dropped lemma on a fresh empty box yields ▷ Q, real slice_empty on B1 a second ▷ Q)
theorem bx_delete_full14 : ¬ drop0% Iris.slice_delete_full 14 := fun h =>
  fupd_later_false (GF := GX BoxF) ⊤ fun {_} => by
    iintro
    imod own_full_alloc (F := BoxF) with ⟨%γ0, Ho⟩
    ihave Hb := box_alloc (GF := GX BoxF) (M := TM) nroot
    ihave Hb2 := box_alloc (GF := GX BoxF) (M := TM) nroot
    imod slice_insert_full (E := ⊤) (q := false) (f := (∅ : TM Bool)) (P := iprop(emp)) (Q := own1 BoxF γ0) (N := nroot)
      (fun _ _ => CoPset.mem_full) $$ [Ho Hb] with ⟨%γ, %Hγ, #Hs, Hb⟩
    · isplitl [Ho]
      · inext; iexact Ho
      · iexact Hb
    imod h (E := ⊤) (q := false) (f := (∅ : TM Bool)) (P := iprop(emp)) (Q := own1 BoxF γ0) (γ := γ) (N := nroot)
      (fun _ _ => CoPset.mem_full) $$ [Hb2] with ⟨%P', H1, _⟩
    · isplitl []
      · iexact Hs
      · iexact Hb2
    imod slice_empty (E := ⊤) (q := false) (P := iprop(own1 BoxF γ0 ∗ emp)) (N := nroot) (fun _ _ => CoPset.mem_full)
      (Iris.Std.LawfulPartialMap.get?_insert_eq rfl) $$ [Hb] with ⟨H2, _⟩
    · isplitl []
      · iexact Hs
      · iexact Hb
    imodintro
    iapply dup_later_false γ0
    isplitl [H1]
    · iexact H1
    · iexact H2

-- `Iris.box_empty` idx 11: necessary (GX with the box functor; box B1 = {γ ↦ true} holding the exclusive resource Q via slice_insert_full; real slice_empty gives ▷ Q and B1 = {γ ↦ false}, then box_empty on it gives ▷ (Q ∗ emp) again)
theorem bx_box_empty11 : ¬ drop0% Iris.box_empty 11 := fun h =>
  fupd_later_false (GF := GX BoxF) ⊤ fun {_} => by
    iintro
    imod own_full_alloc (F := BoxF) with ⟨%γ0, Ho⟩
    ihave Hb := box_alloc (GF := GX BoxF) (M := TM) nroot
    imod slice_insert_full (E := ⊤) (q := false) (f := (∅ : TM Bool)) (P := iprop(emp)) (Q := own1 BoxF γ0) (N := nroot)
      (fun _ _ => CoPset.mem_full) $$ [Ho Hb] with ⟨%γ, %Hγ, #Hs, Hb⟩
    · isplitl [Ho]
      · inext; iexact Ho
      · iexact Hb
    imod slice_empty (E := ⊤) (q := false) (P := iprop(own1 BoxF γ0 ∗ emp)) (N := nroot) (fun _ _ => CoPset.mem_full)
      (Iris.Std.LawfulPartialMap.get?_insert_eq rfl) $$ [Hb] with ⟨H2, Hb⟩
    · isplitl []
      · iexact Hs
      · iexact Hb
    imod h ⊤ (f := Iris.Std.insert (Iris.Std.insert (∅ : TM Bool) γ true) γ false) (P := iprop(own1 BoxF γ0 ∗ emp)) (N := nroot)
      (fun _ _ => CoPset.mem_full) $$ [Hb] with ⟨H1, _⟩
    · iapply laterIf_false_elim
      iexact Hb
    imodintro
    iapply dup_later_false γ0
    isplitl [H1]
    · iapply later_mono sep_elim_left
      iexact H1
    · iexact H2

-- `Iris.slice_iff` idx 16: necessary (GX with the box functor; box B1 = {γ ↦ true} holding the exclusive resource Q via slice_insert_full; the dropped lemma on a fresh empty box (b = true, Q' = Q) creates a full slice γ', real slice_empty on it and on B1: two copies)
theorem bx_iff16 : ¬ drop0% Iris.slice_iff 16 := fun h =>
  fupd_later_false (GF := GX BoxF) ⊤ fun {_} => by
    iintro
    imod own_full_alloc (F := BoxF) with ⟨%γ0, Ho⟩
    ihave Hb := box_alloc (GF := GX BoxF) (M := TM) nroot
    ihave Hb2 := box_alloc (GF := GX BoxF) (M := TM) nroot
    imod slice_insert_full (E := ⊤) (q := false) (f := (∅ : TM Bool)) (P := iprop(emp)) (Q := own1 BoxF γ0) (N := nroot)
      (fun _ _ => CoPset.mem_full) $$ [Ho Hb] with ⟨%γ, %Hγ, #Hs, Hb⟩
    · isplitl [Ho]
      · inext; iexact Ho
      · iexact Hb
    imod h ⊤ false (∅ : TM Bool) iprop(emp) (own1 BoxF γ0) (own1 BoxF γ0) γ true nroot (fun _ _ => CoPset.mem_full) $$ [Hb2]
      with ⟨%γ', %P', _, _, #Hs', Hb2⟩
    · isplitl []
      · imodintro
        inext
        isplit
        · iintro H; iexact H
        · iintro H; iexact H
      · isplitl []
        · iexact Hs
        · iexact Hb2
    imod slice_empty (E := ⊤) (q := false) (N := nroot) (fun _ _ => CoPset.mem_full)
      (Iris.Std.LawfulPartialMap.get?_insert_eq rfl) $$ [Hb2] with ⟨H1, _⟩
    · isplitl []
      · iexact Hs'
      · iexact Hb2
    imod slice_empty (E := ⊤) (q := false) (P := iprop(own1 BoxF γ0 ∗ emp)) (N := nroot) (fun _ _ => CoPset.mem_full)
      (Iris.Std.LawfulPartialMap.get?_insert_eq rfl) $$ [Hb] with ⟨H2, _⟩
    · isplitl []
      · iexact Hs
      · iexact Hb
    imodintro
    iapply dup_later_false γ0
    isplitl [H1]
    · iexact H1
    · iexact H2

-- `Iris.slice_combine` idx 17: necessary (GX with the box functor; box B1 = {γ ↦ true} holding the exclusive resource Q via slice_insert_full; γ1 = γ2 = γ: the combined slice holds Q ∗ Q, real slice_empty gives ▷ (Q ∗ Q))
theorem bx_combine17 : ¬ drop0% Iris.slice_combine 17 := fun h =>
  fupd_later_false (GF := GX BoxF) ⊤ fun {_} => by
    iintro
    imod own_full_alloc (F := BoxF) with ⟨%γ0, Ho⟩
    ihave Hb := box_alloc (GF := GX BoxF) (M := TM) nroot
    imod slice_insert_full (E := ⊤) (q := false) (f := (∅ : TM Bool)) (P := iprop(emp)) (Q := own1 BoxF γ0) (N := nroot)
      (fun _ _ => CoPset.mem_full) $$ [Ho Hb] with ⟨%γ, %Hγ, #Hs, Hb⟩
    · isplitl [Ho]
      · inext; iexact Ho
      · iexact Hb
    imod h ⊤ (q := false) (Q1 := own1 BoxF γ0) (Q2 := own1 BoxF γ0) (γ1 := γ) (γ2 := γ) (b := true) (N := nroot)
      (fun _ _ => CoPset.mem_full) (Iris.Std.LawfulPartialMap.get?_insert_eq rfl) (Iris.Std.LawfulPartialMap.get?_insert_eq rfl)
      $$ [Hb] with ⟨%γ', _, #Hs', Hb⟩
    · isplitl []
      · iexact Hs
      · isplitl []
        · iexact Hs
        · iexact Hb
    imod slice_empty (E := ⊤) (q := false) (N := nroot) (fun _ _ => CoPset.mem_full)
      (Iris.Std.LawfulPartialMap.get?_insert_eq rfl) $$ [Hb] with ⟨H1, _⟩
    · isplitl []
      · iexact Hs'
      · iexact Hb
    imodintro
    iapply dup_later_false γ0
    iapply later_sep.mp
    iexact H1

-- `Iris.slice_split` idx 17: necessary (box B1 = {γ ↦ true} with slice (True ∗ Q); the dropped lemma on a fresh empty box (b = true) creates full slices, real slice_empty on γ2 and on B1: two copies of Q)
theorem bx_split17 : ¬ drop0% Iris.slice_split 17 := fun h =>
  fupd_later_false (GF := GX BoxF) ⊤ fun {_} => by
    iintro
    imod own_full_alloc (F := BoxF) with ⟨%γ0, Ho⟩
    ihave Hb := box_alloc (GF := GX BoxF) (M := TM) nroot
    ihave Hb2 := box_alloc (GF := GX BoxF) (M := TM) nroot
    imod slice_insert_full (E := ⊤) (q := false) (f := (∅ : TM Bool)) (P := iprop(emp)) (Q := iprop(True ∗ own1 BoxF γ0)) (N := nroot)
      (fun _ _ => CoPset.mem_full) $$ [Ho Hb] with ⟨%γ, %Hγ, #Hs, Hb⟩
    · isplitl [Ho]
      · inext; isplitl []
        · itrivial
        · iexact Ho
      · iexact Hb
    imod h (E := ⊤) (q := false) (f := (∅ : TM Bool)) (P := iprop(emp)) (Q1 := iprop(True)) (Q2 := own1 BoxF γ0) (γ := γ)
      (b := true) (N := nroot) (fun _ _ => CoPset.mem_full) $$ [Hb2] with ⟨%γ1, %γ2, _, _, _, _, #Hs2, Hb2⟩
    · isplitl []
      · iexact Hs
      · iexact Hb2
    imod slice_empty (E := ⊤) (q := false) (N := nroot) (fun _ _ => CoPset.mem_full)
      (Iris.Std.LawfulPartialMap.get?_insert_eq rfl) $$ [Hb2] with ⟨H1, _⟩
    · isplitl []
      · iexact Hs2
      · iexact Hb2
    imod slice_empty (E := ⊤) (q := false) (P := iprop(iprop(True ∗ own1 BoxF γ0) ∗ emp)) (N := nroot) (fun _ _ => CoPset.mem_full)
      (Iris.Std.LawfulPartialMap.get?_insert_eq rfl) $$ [Hb] with ⟨H2, _⟩
    · isplitl []
      · iexact Hs
      · iexact Hb
    imodintro
    iapply dup_later_false γ0
    isplitl [H1]
    · iexact H1
    · iapply later_mono sep_elim_right
      iexact H2

-- `Iris.slice_combine` idx 18: necessary (box {γ1 ↦ true, γ2 ↦ true} with slices Q (exclusive), True; delete_full γ1 gives ▷ Q and a box without γ1; combining there yields a full slice Q ∗ True, emptied: second copy)
theorem bx_combine18 : ¬ drop0% Iris.slice_combine 18 := fun h =>
  fupd_later_false (GF := GX BoxF) ⊤ fun {_} => by
    iintro
    imod own_full_alloc (F := BoxF) with ⟨%γ0, Ho⟩
    ihave Hb := box_alloc (GF := GX BoxF) (M := TM) nroot
    imod slice_insert_full (E := ⊤) (q := false) (f := (∅ : TM Bool)) (P := iprop(emp)) (Q := own1 BoxF γ0) (N := nroot)
      (fun _ _ => CoPset.mem_full) $$ [Ho Hb] with ⟨%γ1, %Hγ1, #Hs1, Hb⟩
    · isplitl [Ho]
      · inext; iexact Ho
      · iexact Hb
    imod slice_insert_full (E := ⊤) (q := false) (Q := iprop(True)) (N := nroot)
      (fun _ _ => CoPset.mem_full) $$ [Hb] with ⟨%γ2, %Hγ2, #Hs2, Hb⟩
    · isplitl []
      · inext; itrivial
      · iexact Hb
    have hne : γ1 ≠ γ2 := fun e => by
      subst e
      rw [Iris.Std.LawfulPartialMap.get?_insert_eq rfl] at Hγ2
      cases Hγ2
    imod slice_delete_full (E := ⊤) (q := false) (N := nroot) (fun _ _ => CoPset.mem_full)
      ((Iris.Std.LawfulPartialMap.get?_insert_ne (Ne.symm hne)).trans (Iris.Std.LawfulPartialMap.get?_insert_eq rfl)) $$ [Hb] with ⟨%P', H2, _, Hb⟩
    · isplitl []
      · iexact Hs1
      · iexact Hb
    imod h ⊤ (q := false) (Q1 := own1 BoxF γ0) (Q2 := iprop(True)) (γ1 := γ1) (γ2 := γ2) (b := true) (N := nroot)
      (fun _ _ => CoPset.mem_full) hne
      ((Iris.Std.LawfulPartialMap.get?_delete_ne hne).trans (Iris.Std.LawfulPartialMap.get?_insert_eq rfl))
      $$ [Hb] with ⟨%γ', _, #Hs', Hb⟩
    · isplitl []
      · iexact Hs1
      · isplitl []
        · iexact Hs2
        · iexact Hb
    imod slice_empty (E := ⊤) (q := false) (N := nroot) (fun _ _ => CoPset.mem_full)
      (Iris.Std.LawfulPartialMap.get?_insert_eq rfl) $$ [Hb] with ⟨H1, _⟩
    · isplitl []
      · iexact Hs'
      · iexact Hb
    imodintro
    iapply dup_later_false γ0
    isplitl [H1]
    · iapply later_mono sep_elim_left
      iexact H1
    · iexact H2

-- `Iris.slice_combine` idx 19: necessary (symmetric to idx 18 (γ2 holds the exclusive resource and is deleted first))
theorem bx_combine19 : ¬ drop0% Iris.slice_combine 19 := fun h =>
  fupd_later_false (GF := GX BoxF) ⊤ fun {_} => by
    iintro
    imod own_full_alloc (F := BoxF) with ⟨%γ0, Ho⟩
    ihave Hb := box_alloc (GF := GX BoxF) (M := TM) nroot
    imod slice_insert_full (E := ⊤) (q := false) (f := (∅ : TM Bool)) (P := iprop(emp)) (Q := own1 BoxF γ0) (N := nroot)
      (fun _ _ => CoPset.mem_full) $$ [Ho Hb] with ⟨%γ2, %Hγ2, #Hs2, Hb⟩
    · isplitl [Ho]
      · inext; iexact Ho
      · iexact Hb
    imod slice_insert_full (E := ⊤) (q := false) (Q := iprop(True)) (N := nroot)
      (fun _ _ => CoPset.mem_full) $$ [Hb] with ⟨%γ1, %Hγ1, #Hs1, Hb⟩
    · isplitl []
      · inext; itrivial
      · iexact Hb
    have hne : γ1 ≠ γ2 := fun e => by
      subst e
      rw [Iris.Std.LawfulPartialMap.get?_insert_eq rfl] at Hγ1
      cases Hγ1
    imod slice_delete_full (E := ⊤) (q := false) (N := nroot) (fun _ _ => CoPset.mem_full)
      ((Iris.Std.LawfulPartialMap.get?_insert_ne hne).trans (Iris.Std.LawfulPartialMap.get?_insert_eq rfl)) $$ [Hb] with ⟨%P', H2, _, Hb⟩
    · isplitl []
      · iexact Hs2
      · iexact Hb
    imod h ⊤ (q := false) (Q1 := iprop(True)) (Q2 := own1 BoxF γ0) (γ1 := γ1) (γ2 := γ2) (b := true) (N := nroot)
      (fun _ _ => CoPset.mem_full) hne
      ((Iris.Std.LawfulPartialMap.get?_delete_ne (Ne.symm hne)).trans (Iris.Std.LawfulPartialMap.get?_insert_eq rfl))
      $$ [Hb] with ⟨%γ', _, #Hs', Hb⟩
    · isplitl []
      · iexact Hs1
      · isplitl []
        · iexact Hs2
        · iexact Hb
    imod slice_empty (E := ⊤) (q := false) (N := nroot) (fun _ _ => CoPset.mem_full)
      (Iris.Std.LawfulPartialMap.get?_insert_eq rfl) $$ [Hb] with ⟨H1, _⟩
    · isplitl []
      · iexact Hs'
      · iexact Hb
    imodintro
    iapply dup_later_false γ0
    isplitl [H1]
    · iapply later_mono sep_elim_right
      iexact H1
    · iexact H2

theorem slice_inv_of {hlc : HasLC} [InvGS_gen hlc (GX BoxF)] {N : Namespace} {γ : SliceName} {Q : IProp (GX BoxF)} :
    slice N γ Q ⊢ Iris.inv N (slice_inv γ Q) := sep_elim_right
theorem box_frag {hlc : HasLC} [InvGS_gen hlc (GX BoxF)] {N : Namespace} {γ : SliceName} {P : IProp (GX BoxF)} :
    box (M := TM) N (Iris.Std.insert (∅ : TM Bool) γ true) P ⊢ box_own_auth γ (ExclAuth.frag (⟨true⟩ : BoolO)) := by
  unfold box
  iintro ⟨%Φ, _, Hm⟩
  have e : (iprop([∗map] k ↦ v ∈ Iris.Std.insert (∅ : TM Bool) γ true, box_own_auth k (ExclAuth.frag (⟨v⟩ : BoolO)) ∗
      box_own_prop k (Φ k) ∗ Iris.inv N (slice_inv k (Φ k))) : IProp (GX BoxF)) ⊢
      iprop(box_own_auth γ (ExclAuth.frag (⟨true⟩ : BoolO)) ∗ box_own_prop γ (Φ γ) ∗ Iris.inv N (slice_inv γ (Φ γ))) :=
    BigSepM.bigSepM_singleton.mp
  ihave Hm2 := e $$ Hm
  icases Hm2 with ⟨H, _, _⟩
  iexact H

-- `Iris.slice_empty` idx 13: necessary (box B1 = {γ ↦ true} holding exclusive Q; open the slice invariant at ⊤: if its flag is false it disagrees with the box fragment, if true it holds Q, and the dropped lemma at E = ⊤ ∖ N gives a second copy)
theorem bx_empty13 : ¬ drop0% Iris.slice_empty 13 := fun h =>
  fupd_later_false (GF := GX BoxF) (⊤ \ ↑nroot) fun {_} => by
    iintro
    imod own_full_alloc (F := BoxF) with ⟨%γ0, Ho⟩
    ihave Hb := box_alloc (GF := GX BoxF) (M := TM) nroot
    imod slice_insert_full (E := ⊤) (q := false) (f := (∅ : TM Bool)) (P := iprop(emp)) (Q := own1 BoxF γ0) (N := nroot)
      (fun _ _ => CoPset.mem_full) $$ [Ho Hb] with ⟨%γ, %Hγ, #Hs, Hb⟩
    · isplitl [Ho]
      · inext; iexact Ho
      · iexact Hb
    ihave #Hi := slice_inv_of $$ Hs
    imod inv_acc (E := ⊤) (N := nroot) (fun _ _ => CoPset.mem_full) $$ Hi with ⟨Hc, _⟩
    unfold slice_inv
    icases Hc with ⟨%b, Ha, Hq⟩
    cases b
    · ihave Hf := (laterIf_false_elim.trans box_frag) $$ Hb
      imodintro
      iapply later_mono ((box_own_auth_agree (b1 := false) (b2 := true)).trans (pure_mono (φ2 := False) (fun e => by cases e)))
      isplitl [Ha]
      · iexact Ha
      · inext; iexact Hf
    · imod h (E := ⊤ \ ↑nroot) (q := false) (P := iprop(own1 BoxF γ0 ∗ emp)) (N := nroot)
        (Iris.Std.LawfulPartialMap.get?_insert_eq rfl) $$ [Hb] with ⟨H1, _⟩
      · isplitl []
        · iexact Hs
        · iexact Hb
      imodintro
      iapply dup_later_false γ0
      isplitl [H1]
      · iexact H1
      · iapply later_mono (show (if true = true then own1 BoxF γ0 else iprop(True)) ⊢ own1 BoxF γ0 from .rfl)
        iexact Hq

-- `Iris.slice_delete_full` idx 13: necessary (box B1 = {γ ↦ true} holding exclusive Q; open the slice invariant at ⊤: if its flag is false it disagrees with the box fragment, if true it holds Q, and the dropped lemma at E = ⊤ ∖ N gives a second copy)
theorem bx_delete_full13 : ¬ drop0% Iris.slice_delete_full 13 := fun h =>
  fupd_later_false (GF := GX BoxF) (⊤ \ ↑nroot) fun {_} => by
    iintro
    imod own_full_alloc (F := BoxF) with ⟨%γ0, Ho⟩
    ihave Hb := box_alloc (GF := GX BoxF) (M := TM) nroot
    imod slice_insert_full (E := ⊤) (q := false) (f := (∅ : TM Bool)) (P := iprop(emp)) (Q := own1 BoxF γ0) (N := nroot)
      (fun _ _ => CoPset.mem_full) $$ [Ho Hb] with ⟨%γ, %Hγ, #Hs, Hb⟩
    · isplitl [Ho]
      · inext; iexact Ho
      · iexact Hb
    ihave #Hi := slice_inv_of $$ Hs
    imod inv_acc (E := ⊤) (N := nroot) (fun _ _ => CoPset.mem_full) $$ Hi with ⟨Hc, _⟩
    unfold slice_inv
    icases Hc with ⟨%b, Ha, Hq⟩
    cases b
    · ihave Hf := (laterIf_false_elim.trans box_frag) $$ Hb
      imodintro
      iapply later_mono ((box_own_auth_agree (b1 := false) (b2 := true)).trans (pure_mono (φ2 := False) (fun e => by cases e)))
      isplitl [Ha]
      · iexact Ha
      · inext; iexact Hf
    · imod h (E := ⊤ \ ↑nroot) (q := false) (P := iprop(own1 BoxF γ0 ∗ emp)) (N := nroot)
        (Iris.Std.LawfulPartialMap.get?_insert_eq rfl) $$ [Hb] with ⟨%P', H1, _, _⟩
      · isplitl []
        · iexact Hs
        · iexact Hb
      imodintro
      iapply dup_later_false γ0
      isplitl [H1]
      · iexact H1
      · iapply later_mono (show (if true = true then own1 BoxF γ0 else iprop(True)) ⊢ own1 BoxF γ0 from .rfl)
        iexact Hq

-- `Iris.box_empty` idx 10: necessary (box B1 = {γ ↦ true} holding exclusive Q; open the slice invariant at ⊤: if its flag is false it disagrees with the box fragment, if true it holds Q, and the dropped lemma at E = ⊤ ∖ N gives a second copy)
theorem bx_box_empty10 : ¬ drop0% Iris.box_empty 10 := fun h =>
  fupd_later_false (GF := GX BoxF) (⊤ \ ↑nroot) fun {_} => by
    iintro
    imod own_full_alloc (F := BoxF) with ⟨%γ0, Ho⟩
    ihave Hb := box_alloc (GF := GX BoxF) (M := TM) nroot
    imod slice_insert_full (E := ⊤) (q := false) (f := (∅ : TM Bool)) (P := iprop(emp)) (Q := own1 BoxF γ0) (N := nroot)
      (fun _ _ => CoPset.mem_full) $$ [Ho Hb] with ⟨%γ, %Hγ, #Hs, Hb⟩
    · isplitl [Ho]
      · inext; iexact Ho
      · iexact Hb
    ihave #Hi := slice_inv_of $$ Hs
    imod inv_acc (E := ⊤) (N := nroot) (fun _ _ => CoPset.mem_full) $$ Hi with ⟨Hc, _⟩
    unfold slice_inv
    icases Hc with ⟨%b, Ha, Hq⟩
    cases b
    · ihave Hf := (laterIf_false_elim.trans box_frag) $$ Hb
      imodintro
      iapply later_mono ((box_own_auth_agree (b1 := false) (b2 := true)).trans (pure_mono (φ2 := False) (fun e => by cases e)))
      isplitl [Ha]
      · iexact Ha
      · inext; iexact Hf
    · imod h (⊤ \ ↑nroot) (f := Iris.Std.insert (∅ : TM Bool) γ true) (P := iprop(own1 BoxF γ0 ∗ emp)) (N := nroot)
        (by
          intro k v hk
          by_cases e : γ = k
          · rw [Iris.Std.LawfulPartialMap.get?_insert_eq e] at hk; cases hk; rfl
          · rw [Iris.Std.LawfulPartialMap.get?_insert_ne e, Iris.Std.LawfulPartialMap.get?_empty] at hk; cases hk) $$ [Hb] with ⟨H1, _⟩
      · iapply laterIf_false_elim
        iexact Hb
      imodintro
      iapply dup_later_false γ0
      isplitl [H1]
      · iapply later_mono sep_elim_left
        iexact H1
      · iapply later_mono (show (if true = true then own1 BoxF γ0 else iprop(True)) ⊢ own1 BoxF γ0 from .rfl)
        iexact Hq

theorem box_frag' {hlc : HasLC} [InvGS_gen hlc (GX BoxF)] {N : Namespace} {f : TM Bool} {γ : SliceName} {b : Bool}
    {P : IProp (GX BoxF)} (hf : Iris.Std.get? f γ = some b) :
    box (M := TM) N f P ⊢ box_own_auth γ (ExclAuth.frag (⟨b⟩ : BoolO)) := by
  unfold box
  iintro ⟨%Φ, _, Hm⟩
  ihave Hm2 := (BigSepM.bigSepM_lookup (Φ := fun γ b => iprop(box_own_auth γ (ExclAuth.frag (⟨b⟩ : BoolO)) ∗
    box_own_prop γ (Φ γ) ∗ Iris.inv N (slice_inv γ (Φ γ)))) hf) $$ Hm
  icases Hm2 with ⟨H, _, _⟩
  iexact H

-- `Iris.slice_fill` idx 13: necessary (box B1 = {γ ↦ true} holding exclusive Q, emptied for real (▷ Q in hand, γ ↦ false); open the slice invariant at ⊤: flag true disagrees with the box, flag false disagrees with the box after the dropped lemma at E = ⊤ ∖ N refills it)
theorem bx_fill13 : ¬ drop0% Iris.slice_fill 13 := fun h =>
  fupd_later_false (GF := GX BoxF) (⊤ \ ↑nroot) fun {_} => by
    iintro
    imod own_full_alloc (F := BoxF) with ⟨%γ0, Ho⟩
    ihave Hb := box_alloc (GF := GX BoxF) (M := TM) nroot
    imod slice_insert_full (E := ⊤) (q := false) (f := (∅ : TM Bool)) (P := iprop(emp)) (Q := own1 BoxF γ0) (N := nroot)
      (fun _ _ => CoPset.mem_full) $$ [Ho Hb] with ⟨%γ, %Hγ, #Hs, Hb⟩
    · isplitl [Ho]
      · inext; iexact Ho
      · iexact Hb
    imod slice_empty (E := ⊤) (q := false) (P := iprop(own1 BoxF γ0 ∗ emp)) (N := nroot) (fun _ _ => CoPset.mem_full)
      (Iris.Std.LawfulPartialMap.get?_insert_eq rfl) $$ [Hb] with ⟨HQ, Hb⟩
    · isplitl []
      · iexact Hs
      · iexact Hb
    ihave #Hi := slice_inv_of $$ Hs
    imod inv_acc (E := ⊤) (N := nroot) (fun _ _ => CoPset.mem_full) $$ Hi with ⟨Hc, _⟩
    unfold slice_inv
    icases Hc with ⟨%b, Ha, _⟩
    cases b
    · imod h (E := ⊤ \ ↑nroot) (q := false) (P := iprop(own1 BoxF γ0 ∗ emp)) (N := nroot)
        (Iris.Std.LawfulPartialMap.get?_insert_eq rfl) $$ [Hb HQ] with Hb
      · isplitl []
        · iexact Hs
        · isplitl [HQ]
          · iexact HQ
          · iexact Hb
      ihave Hf := (laterIf_false_elim.trans (box_frag' (Iris.Std.LawfulPartialMap.get?_insert_eq rfl))) $$ Hb
      imodintro
      iapply later_mono ((box_own_auth_agree (b1 := false) (b2 := true)).trans (pure_mono (φ2 := False) (fun e => by cases e)))
      isplitl [Ha]
      · iexact Ha
      · inext; iexact Hf
    · ihave Hf := (laterIf_false_elim.trans (box_frag' (Iris.Std.LawfulPartialMap.get?_insert_eq rfl))) $$ Hb
      imodintro
      iapply later_mono ((box_own_auth_agree (b1 := true) (b2 := false)).trans (pure_mono (φ2 := False) (fun e => by cases e)))
      isplitl [Ha]
      · iexact Ha
      · inext; iexact Hf

-- `Iris.box_fill` idx 10: necessary (box B1 = {γ ↦ true} holding exclusive Q, emptied for real (▷ Q in hand, γ ↦ false); open the slice invariant at ⊤: flag true disagrees with the box, flag false disagrees with the box after the dropped lemma at E = ⊤ ∖ N refills it)
theorem bx_box_fill10 : ¬ drop0% Iris.box_fill 10 := fun h =>
  fupd_later_false (GF := GX BoxF) (⊤ \ ↑nroot) fun {_} => by
    iintro
    imod own_full_alloc (F := BoxF) with ⟨%γ0, Ho⟩
    ihave Hb := box_alloc (GF := GX BoxF) (M := TM) nroot
    imod slice_insert_full (E := ⊤) (q := false) (f := (∅ : TM Bool)) (P := iprop(emp)) (Q := own1 BoxF γ0) (N := nroot)
      (fun _ _ => CoPset.mem_full) $$ [Ho Hb] with ⟨%γ, %Hγ, #Hs, Hb⟩
    · isplitl [Ho]
      · inext; iexact Ho
      · iexact Hb
    imod slice_empty (E := ⊤) (q := false) (P := iprop(own1 BoxF γ0 ∗ emp)) (N := nroot) (fun _ _ => CoPset.mem_full)
      (Iris.Std.LawfulPartialMap.get?_insert_eq rfl) $$ [Hb] with ⟨HQ, Hb⟩
    · isplitl []
      · iexact Hs
      · iexact Hb
    ihave #Hi := slice_inv_of $$ Hs
    imod inv_acc (E := ⊤) (N := nroot) (fun _ _ => CoPset.mem_full) $$ Hi with ⟨Hc, _⟩
    unfold slice_inv
    icases Hc with ⟨%b, Ha, _⟩
    cases b
    · imod h (⊤ \ ↑nroot) (f := Iris.Std.insert (Iris.Std.insert (∅ : TM Bool) γ true) γ false) (P := iprop(own1 BoxF γ0 ∗ emp))
        (N := nroot) $$ [Hb HQ] with Hb
      · isplitl [Hb]
        · iapply laterIf_false_elim
          iexact Hb
        · inext
          isplitl [HQ]
          · iexact HQ
          · itrivial
      ihave Hf := (box_frag' (γ := γ) (b := true) (by
        rw [Iris.Std.LawfulPartialMap.get?_map, Iris.Std.LawfulPartialMap.get?_insert_eq rfl]; rfl)) $$ Hb
      imodintro
      iapply later_mono ((box_own_auth_agree (b1 := false) (b2 := true)).trans (pure_mono (φ2 := False) (fun e => by cases e)))
      isplitl [Ha]
      · iexact Ha
      · inext; iexact Hf
    · ihave Hf := (laterIf_false_elim.trans (box_frag' (Iris.Std.LawfulPartialMap.get?_insert_eq rfl))) $$ Hb
      imodintro
      iapply later_mono ((box_own_auth_agree (b1 := true) (b2 := false)).trans (pure_mono (φ2 := False) (fun e => by cases e)))
      isplitl [Ha]
      · iexact Ha
      · inext; iexact Hf

section InsFull
open BI ORA Agree OFE Iris.UPred IProp Iris.Std ProofMode COFE Auth ExclAuth Excl PartialMap BigSepM
-- `Iris.slice_insert_full` idx 12: removable (re-proof of slice_insert_empty allocating the slice already full (flag true, ▷ Q stored by inv_alloc, which works at any mask); slice_fill and its mask condition are not needed)
theorem bx_ins_full : drop% Iris.slice_insert_full 12 := by
  intro hlc GF _ _ M _ E q f P Q N
  iintro ⟨HQ, Hbox⟩
  unfold box
  icases Hbox with ⟨%Φ, #Heq, H⟩
  imod (iOwn_alloc_cofinite (F := BoxF) ((((●E (⟨true⟩ : BoolO)), none) • ((◯E (⟨true⟩ : BoolO)), none)) •
        (unit, some (toAgree (Later.next Q)))) ((toList f).map Prod.fst)) with ⟨%γ, %Hγ, Hown⟩
  · exact ⟨ExclAuth.valid, Agree.toAgree_valid⟩
  have hfresh : get? f γ = none := by
    rw [Option.eq_none_iff_forall_not_mem]
    exact fun v h => Hγ (List.mem_map_of_mem (toList_get.mpr h))
  icases iOwn_op $$ Hown with ⟨⟨Hauth, Hfrag⟩, #Hprop⟩
  imod inv_alloc N E (slice_inv γ Q) $$ [Hauth HQ] with #Hinv
  · inext
    unfold slice_inv box_own_auth; iexists true
    simp only [ite_true]
    iframe
  imodintro
  iexists γ
  unfold slice; iframe %hfresh Hinv
  isplit
  · unfold box_own_prop; iframe Hprop
  iexists (fun γ'' => if γ'' = γ then Q else Φ γ'')
  inext
  isplit
  · inext
    irewrite [Heq]
    · exact ⟨fun _ _ _ H => (NonExpansive₂.ne_left internalEq _).ne ((sep_ne.ne_right _ _).ne H)⟩
    rw [bigSepM_fn_insert_key hfresh]; exact internalEq.refl
  · rw [(bigSepM_fn_insert (g := fun k b P' =>
        iprop% box_own_auth k (◯E (⟨b⟩ : BoolO)) ∗ box_own_prop k P' ∗ inv N (slice_inv k P')) hfresh)]
    unfold box_own_prop box_own_auth; iframe H Hfrag Hprop Hinv
end InsFull

-- `Iris.slice_fill` idx 14: necessary (box B1 = {γ ↦ true} with exclusive Q emptied for real (B1 says γ ↦ false); the dropped lemma refills γ into a fresh empty box (γ ↦ true); the slice invariant flag disagrees with one of the two boxes)
theorem bx_fill14 : ¬ drop0% Iris.slice_fill 14 := fun h =>
  fupd_later_false (GF := GX BoxF) (⊤ \ ↑nroot) fun {_} => by
    iintro
    imod own_full_alloc (F := BoxF) with ⟨%γ0, Ho⟩
    ihave Hb := box_alloc (GF := GX BoxF) (M := TM) nroot
    ihave Hb2 := box_alloc (GF := GX BoxF) (M := TM) nroot
    imod slice_insert_full (E := ⊤) (q := false) (f := (∅ : TM Bool)) (P := iprop(emp)) (Q := own1 BoxF γ0) (N := nroot)
      (fun _ _ => CoPset.mem_full) $$ [Ho Hb] with ⟨%γ, %Hγ, #Hs, Hb⟩
    · isplitl [Ho]
      · inext; iexact Ho
      · iexact Hb
    imod slice_empty (E := ⊤) (q := false) (P := iprop(own1 BoxF γ0 ∗ emp)) (N := nroot) (fun _ _ => CoPset.mem_full)
      (Iris.Std.LawfulPartialMap.get?_insert_eq rfl) $$ [Hb] with ⟨HQ, Hb⟩
    · isplitl []
      · iexact Hs
      · iexact Hb
    imod h (E := ⊤) (q := false) (f := (∅ : TM Bool)) (γ := γ) (P := iprop(emp)) (Q := own1 BoxF γ0) (N := nroot)
      (fun _ _ => CoPset.mem_full) $$ [Hb2 HQ] with Hb2
    · isplitl []
      · iexact Hs
      · isplitl [HQ]
        · iexact HQ
        · iexact Hb2
    ihave #Hi := slice_inv_of $$ Hs
    imod inv_acc (E := ⊤) (N := nroot) (fun _ _ => CoPset.mem_full) $$ Hi with ⟨Hc, _⟩
    unfold slice_inv
    icases Hc with ⟨%b, Ha, _⟩
    cases b
    · ihave Hf := (laterIf_false_elim.trans (box_frag' (Iris.Std.LawfulPartialMap.get?_insert_eq rfl))) $$ Hb2
      imodintro
      iapply later_mono ((box_own_auth_agree (b1 := false) (b2 := true)).trans (pure_mono (φ2 := False) (fun e => by cases e)))
      isplitl [Ha]
      · iexact Ha
      · inext; iexact Hf
    · ihave Hf := (laterIf_false_elim.trans (box_frag' (Iris.Std.LawfulPartialMap.get?_insert_eq rfl))) $$ Hb
      imodintro
      iapply later_mono ((box_own_auth_agree (b1 := true) (b2 := false)).trans (pure_mono (φ2 := False) (fun e => by cases e)))
      isplitl [Ha]
      · iexact Ha
      · inext; iexact Hf

namespace W7c0
open Iris Iris.BI
/-- e unit, p, q, s valid, t invalid and absorbing; all other products t; order: reflexive, p ≤ s, q ≤ s, everything ≤ t. Not OrdInc. -/
inductive TQ | e | p | q | s | t deriving DecidableEq
def TQ.op : TQ → TQ → TQ
  | .e, y => y
  | x, .e => x
  | _, _ => .t
def TQ.le : TQ → TQ → Bool
  | _, .t => true
  | .e, .e => true
  | .p, .p => true
  | .q, .q => true
  | .s, .s => true
  | .p, .s => true
  | .q, .s => true
  | _, _ => false
instance : OFE TQ := OFE.ofDiscrete TQ
instance : OFE.Discrete TQ := ⟨id⟩
@[instance_reducible] def tqData : DiscreteORAData TQ where
  pcore := fun _ => some .e
  op := TQ.op
  Valid := fun x => x ≠ .t
  Order := fun x y => TQ.le x y = true
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
  pcore_op_left := by intro x cx h; cases h; cases x <;> rfl
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := by intro x y; cases x <;> cases y <;> decide
  ord_trans := by intro x y z; cases x <;> cases y <;> cases z <;> decide
  op_mono_left := by intro x y z; cases x <;> cases y <;> cases z <;> decide
  valid_of_ord := by intro x y; cases x <;> cases y <;> decide
  pcore_mono := by intro x y cx h1 h2; cases h2; exact ⟨.e, rfl, by decide⟩
  pcore_order_op := by intro x cx h y; cases h; exact ⟨.e, rfl, by decide⟩
  pcore_increasing := by intro x cx h y; cases h; cases y <;> decide
  increasing_closed := by
    intro x y hx hxy w
    have h1 := hx .e
    cases x <;> cases y <;> cases w <;> simp_all [TQ.le, TQ.op]
instance tqORA : ORA TQ := ORA.ofDiscreteORAData tqData
instance : OrderRefl TQ := ⟨fun x => show TQ.le x x = true by cases x <;> decide⟩
instance tqUORA : UORA TQ where
  unit := .e
  unit_valid := show TQ.e ≠ .t by decide
  unit_left_id := rfl
  pcore_unit := rfl
end W7c0
open W7c0 Iris Iris.BI

-- `UPred.ownM_forall` idx 3: necessary (at A : Type (at Prop the claim holds); UPred TQ: e unit, p, q, s, t invalid absorbing, other products t, order p ≤ s, q ≤ s (not OrdInc); f true = p, f false = q at resource s: no z ≤ s is a multiple of both)
theorem u_11 : ¬ ∀ {M : Type} [UORA M] {A : Type} (f : A → M),
    (iprop(∀ a, UPred.ownM (f a)) : UPred M) ⊢ iprop(∃ z, UPred.ownM z ∧ (∀ a, ∃ xf, z ≡ f a • xf)) := fun h => by
  have H := @h TQ _ Bool (fun b => if b then TQ.p else TQ.q) 0 ⟨.s, show TQ.s ≠ .t by decide⟩ (by
    rintro P ⟨b, rfl⟩
    cases b <;> exact rfl)
  obtain ⟨_, ⟨z, rfl⟩, hz, hall⟩ := H
  obtain ⟨_, ⟨x1, rfl⟩, e1⟩ := hall _ ⟨true, rfl⟩
  obtain ⟨_, ⟨x2, rfl⟩, e2⟩ := hall _ ⟨false, rfl⟩
  have e1' : z = TQ.op TQ.p x1 := OFE.Discrete.discrete e1
  have e2' : z = TQ.op TQ.q x2 := OFE.Discrete.discrete e2
  have hz' : TQ.le z TQ.s = true := hz
  subst e1'
  cases x1 <;> cases x2 <;> simp_all [TQ.op, TQ.le]
