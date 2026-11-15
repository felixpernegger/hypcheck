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
namespace W2c5
open Iris Iris.OFE Iris.Algebra Iris.Std

/-- Discrete OFE on naturals (fresh structure). -/
structure AN where v : Nat
instance anOFE : OFE AN := OFE.ofDiscrete AN
instance : Inhabited AN := ⟨⟨0⟩⟩
def addAN (a b : AN) : AN := ⟨a.v + b.v⟩
instance anAdd : MonoidOps addAN ⟨0⟩ where
  op_ne := ⟨fun _ _ _ h _ _ h' => by cases h; cases h'; rfl⟩
  op_assoc := by intro a b c; simp [addAN, Nat.add_assoc]
  op_comm := by intro a b; simp [addAN, Nat.add_comm]
  op_left_id := by intro a; simp [addAN]
/-- Constant-zero operation: unit 0 is no left identity. -/
def zAN (_ _ : AN) : AN := ⟨0⟩
theorem z_bad : ¬ MonoidOps zAN ⟨0⟩ := fun h => absurd (congrArg AN.v (h.op_left_id (a := ⟨1⟩))) (by decide)
/-- A non-medial operation a*a + b. -/
def sqAN (a b : AN) : AN := ⟨a.v * a.v + b.v⟩
/-- The order relation on AN, preserved by addition. -/
def leAN (x y : AN) : Prop := x.v ≤ y.v
/-- id : (AN,+) → (AN,+) is a weak homomorphism for ≤. -/
instance whLe : WeakMonoidHomomorphism addAN addAN ⟨0⟩ ⟨0⟩ leAN id where
  rel_refl := Nat.le_refl _
  rel_trans := Nat.le_trans
  op_proper := fun h1 h2 => Nat.add_le_add h1 h2
  map_ne := ⟨fun _ _ _ h => h⟩
  map_op := Nat.le_refl _

/-- Truncation OFE on naturals: dist n x y iff min x (n+1) = min y (n+1). -/
structure TN where v : Nat
instance tnOFE : OFE TN where
  Dist n x y := min x.v (n+1) = min y.v (n+1)
  dist_eqv := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩
  eq_dist' {x y} := ⟨fun h n => h ▸ rfl, fun h => by
      cases x with | mk a => cases y with | mk b =>
      have h' : min a (a+b+1) = min b (a+b+1) := h (a+b)
      simp only [TN.mk.injEq]; omega⟩
  dist_lt {n x y m} h hm := by
    have h' : min x.v (n+1) = min y.v (n+1) := h
    show min x.v (m+1) = min y.v (m+1); omega
theorem tn12 : (⟨1⟩ : TN) ≡{0}≡ ⟨2⟩ := rfl
def addTN (a b : TN) : TN := ⟨a.v + b.v⟩
/-- Addition on the truncation OFE is a (non-expansive) commutative monoid. -/
instance tnAdd : MonoidOps addTN ⟨0⟩ where
  op_ne := ⟨fun n x₁ x₂ h y₁ y₂ h' => by
    have a : min x₁.v (n+1) = min x₂.v (n+1) := h
    have b : min y₁.v (n+1) = min y₂.v (n+1) := h'
    show min (x₁.v + y₁.v) (n+1) = min (x₂.v + y₂.v) (n+1); omega⟩
  op_assoc := by intro a b c; simp [addTN, Nat.add_assoc]
  op_comm := by intro a b; simp [addTN, Nat.add_comm]
  op_left_id := by intro a; simp [addTN]

open Iris.Mra in
theorem nil_ne {α : Type} (R : α → α → Prop) (a b : α) (h : R a b) : (Mra.mk [] : Mra R) ≠ toMra b :=
  fun e => by
    have hb : below a (toMra (R := R) b) := (below_toMra a b).mpr h
    rw [← e] at hb
    obtain ⟨_, hm, _⟩ := hb
    cases hm
open Iris.Mra in
theorem toMra_ne {α : Type} (R : α → α → Prop) (a b : α) (h : R a a) (h' : ¬ R a b) :
    toMra (R := R) a ≠ toMra b := fun e =>
  h' ((below_toMra a b).mp (e ▸ (below_toMra a a).mpr h))
open Iris.Mra in
theorem toMra_eq_of {α : Type} {R : α → α → Prop} {a b : α} (h : ∀ c, R c a ↔ R c b) :
    toMra (R := R) a = toMra b :=
  eq_of_below_iff fun c => (below_toMra c a).trans ((h c).trans (below_toMra c b).symm)
theorem neq_hrel : ∀ {a a' b b' : Bool}, a ≠ a' → b ≠ b' → (a = b ↔ a' = b') := by decide
theorem eq_hrel : ∀ {a a' b b' : Bool}, a = a' → b = b' → (a = b ↔ a' = b') := by
  intro a a' b b' h1 h2; subst h1; subst h2; exact Iff.rfl

end W2c5

open Iris Iris.OFE Iris.Algebra Iris.Std W2c5

-- `Iris.Algebra.MonoidOps.op_op_op_comm` idx 4: necessary (op a b = a*a + b on AN; a = c = 1, b = d = 0: 2 vs 4)
theorem w2c5_1 : ¬ drop0% Iris.Algebra.MonoidOps.op_op_op_comm 4 := fun H =>
  absurd (congrArg AN.v (@H AN _ ⟨0⟩ sqAN ⟨1⟩ ⟨0⟩ ⟨1⟩ ⟨0⟩)) (by decide)
-- `Iris.Algebra.MonoidOps.op_dist` idx 10: necessary (discrete (AN,+): a = 0, a' = 1, b = b' = 0)
theorem w2c5_2 : ¬ drop0% Iris.Algebra.MonoidOps.op_dist 10 := fun H =>
  absurd (congrArg AN.v (@H AN _ ⟨0⟩ addAN 0 ⟨0⟩ ⟨1⟩ ⟨0⟩ ⟨0⟩ anAdd rfl)) (by decide)
-- `Iris.Algebra.MonoidOps.op_dist` idx 11: necessary (discrete (AN,+): a = a' = 0, b = 0, b' = 1)
theorem w2c5_3 : ¬ drop0% Iris.Algebra.MonoidOps.op_dist 11 := fun H =>
  absurd (congrArg AN.v (@H AN _ ⟨0⟩ addAN 0 ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨1⟩ anAdd rfl)) (by decide)
-- `Iris.Algebra.WeakMonoidHomomorphism.rel_refl` idx 8: necessary (op₁ = constant 0 on AN: no left identity)
theorem w2c5_4 : ¬ indep0% Iris.Algebra.WeakMonoidHomomorphism.rel_refl 8 := fun H =>
  z_bad (@H AN AN _ _ zAN addAN ⟨0⟩ ⟨0⟩ anAdd Eq id ⟨0⟩)
-- `Iris.Algebra.WeakMonoidHomomorphism.rel_refl` idx 9: necessary (op₂ = constant 0 on AN: no left identity)
theorem w2c5_5 : ¬ indep0% Iris.Algebra.WeakMonoidHomomorphism.rel_refl 9 := fun H =>
  z_bad (@H AN AN _ _ addAN zAN ⟨0⟩ ⟨0⟩ anAdd Eq id ⟨0⟩)
-- `Iris.Algebra.WeakMonoidHomomorphism.rel_refl` idx 12: necessary (R = False)
theorem w2c5_6 : ¬ drop0% Iris.Algebra.WeakMonoidHomomorphism.rel_refl 12 := fun H =>
  @H AN AN _ _ addAN addAN ⟨0⟩ ⟨0⟩ anAdd anAdd (fun _ _ => False) id ⟨0⟩
-- `Iris.Algebra.WeakMonoidHomomorphism.rel_trans` idx 8: necessary (op₁ = constant 0 on AN: no left identity)
theorem w2c5_7 : ¬ indep0% Iris.Algebra.WeakMonoidHomomorphism.rel_trans 8 := fun H =>
  z_bad (@H AN AN _ _ zAN addAN ⟨0⟩ ⟨0⟩ anAdd Eq id ⟨0⟩ ⟨0⟩ ⟨0⟩ rfl rfl)
-- `Iris.Algebra.WeakMonoidHomomorphism.rel_trans` idx 9: necessary (op₂ = constant 0 on AN: no left identity)
theorem w2c5_8 : ¬ indep0% Iris.Algebra.WeakMonoidHomomorphism.rel_trans 9 := fun H =>
  z_bad (@H AN AN _ _ addAN zAN ⟨0⟩ ⟨0⟩ anAdd Eq id ⟨0⟩ ⟨0⟩ ⟨0⟩ rfl rfl)
-- `Iris.Algebra.WeakMonoidHomomorphism.rel_trans` idx 12: necessary (R x y := y = x+1; 0 R 1 R 2 but not 0 R 2)
theorem w2c5_9 : ¬ drop0% Iris.Algebra.WeakMonoidHomomorphism.rel_trans 12 := fun H =>
  absurd (@H AN AN _ _ addAN addAN ⟨0⟩ ⟨0⟩ anAdd anAdd (fun x y => y.v = x.v + 1) id ⟨0⟩ ⟨1⟩ ⟨2⟩ rfl rfl)
    (by decide)
-- `Iris.Algebra.WeakMonoidHomomorphism.rel_trans` idx 16: necessary (id on (AN,+) is a weak homomorphism for ≤; a = 1, b = c = 0)
theorem w2c5_10 : ¬ drop0% Iris.Algebra.WeakMonoidHomomorphism.rel_trans 16 := fun H =>
  absurd (@H AN AN _ _ addAN addAN ⟨0⟩ ⟨0⟩ anAdd anAdd leAN id whLe ⟨1⟩ ⟨0⟩ ⟨0⟩ (Nat.le_refl 0))
    (by simp [leAN])
-- `Iris.Algebra.WeakMonoidHomomorphism.rel_trans` idx 17: necessary (id on (AN,+) is a weak homomorphism for ≤; a = b = 1, c = 0)
theorem w2c5_11 : ¬ drop0% Iris.Algebra.WeakMonoidHomomorphism.rel_trans 17 := fun H =>
  absurd (@H AN AN _ _ addAN addAN ⟨0⟩ ⟨0⟩ anAdd anAdd leAN id whLe ⟨1⟩ ⟨1⟩ ⟨0⟩ (Nat.le_refl 1))
    (by simp [leAN])
-- `Iris.Algebra.WeakMonoidHomomorphism.op_proper` idx 8: necessary (op₁ = constant 0 on AN: no left identity)
theorem w2c5_12 : ¬ indep0% Iris.Algebra.WeakMonoidHomomorphism.op_proper 8 := fun H =>
  z_bad (@H AN AN _ _ zAN addAN ⟨0⟩ ⟨0⟩ anAdd Eq id ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨0⟩ rfl rfl)
-- `Iris.Algebra.WeakMonoidHomomorphism.op_proper` idx 9: necessary (op₂ = constant 0 on AN: no left identity)
theorem w2c5_13 : ¬ indep0% Iris.Algebra.WeakMonoidHomomorphism.op_proper 9 := fun H =>
  z_bad (@H AN AN _ _ addAN zAN ⟨0⟩ ⟨0⟩ anAdd Eq id ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨0⟩ rfl rfl)
-- `Iris.Algebra.WeakMonoidHomomorphism.op_proper` idx 12: necessary (R x y := x = 1 ∧ y = 1; all four values 1)
theorem w2c5_14 : ¬ drop0% Iris.Algebra.WeakMonoidHomomorphism.op_proper 12 := fun H =>
  absurd (@H AN AN _ _ addAN addAN ⟨0⟩ ⟨0⟩ anAdd anAdd (fun x y => x.v = 1 ∧ y.v = 1) id ⟨1⟩ ⟨1⟩ ⟨1⟩ ⟨1⟩
    ⟨rfl, rfl⟩ ⟨rfl, rfl⟩) (by decide)
-- `Iris.Algebra.WeakMonoidHomomorphism.op_proper` idx 17: necessary (id on (AN,+) for ≤; a = 1, a' = 0, b = b' = 0)
theorem w2c5_15 : ¬ drop0% Iris.Algebra.WeakMonoidHomomorphism.op_proper 17 := fun H =>
  absurd (@H AN AN _ _ addAN addAN ⟨0⟩ ⟨0⟩ anAdd anAdd leAN id whLe ⟨1⟩ ⟨0⟩ ⟨0⟩ ⟨0⟩ (Nat.le_refl 0))
    (by simp [leAN, addAN])
-- `Iris.Algebra.WeakMonoidHomomorphism.op_proper` idx 18: necessary (id on (AN,+) for ≤; a = a' = 0, b = 1, b' = 0)
theorem w2c5_16 : ¬ drop0% Iris.Algebra.WeakMonoidHomomorphism.op_proper 18 := fun H =>
  absurd (@H AN AN _ _ addAN addAN ⟨0⟩ ⟨0⟩ anAdd anAdd leAN id whLe ⟨0⟩ ⟨0⟩ ⟨1⟩ ⟨0⟩ (Nat.le_refl 0))
    (by simp [leAN, addAN])
-- `Iris.Algebra.WeakMonoidHomomorphism.map_ne` idx 8: necessary (op₁ = constant 0 on AN: no left identity)
theorem w2c5_17 : ¬ indep0% Iris.Algebra.WeakMonoidHomomorphism.map_ne 8 := fun H =>
  z_bad (@H AN AN _ _ zAN addAN ⟨0⟩ ⟨0⟩ anAdd Eq id)
-- `Iris.Algebra.WeakMonoidHomomorphism.map_ne` idx 9: necessary (op₂ = constant 0 on AN: no left identity)
theorem w2c5_18 : ¬ indep0% Iris.Algebra.WeakMonoidHomomorphism.map_ne 9 := fun H =>
  z_bad (@H AN AN _ _ addAN zAN ⟨0⟩ ⟨0⟩ anAdd Eq id)
-- `Iris.Algebra.WeakMonoidHomomorphism.map_ne` idx 12: necessary (f : TN → AN, x ↦ x.v; 1 and 2 agree at step 0 in TN only)
theorem w2c5_19 : ¬ drop0% Iris.Algebra.WeakMonoidHomomorphism.map_ne 12 := fun H =>
  absurd (congrArg AN.v ((@H TN AN _ _ addTN addAN ⟨0⟩ ⟨0⟩ tnAdd anAdd Eq (fun x => ⟨x.v⟩)).ne tn12))
    (by decide)
-- `Iris.Algebra.WeakMonoidHomomorphism.map_op` idx 8: necessary (op₁ = constant 0 on AN: no left identity)
theorem w2c5_20 : ¬ indep0% Iris.Algebra.WeakMonoidHomomorphism.map_op 8 := fun H =>
  z_bad (@H AN AN _ _ zAN addAN ⟨0⟩ ⟨0⟩ anAdd Eq id ⟨0⟩ ⟨0⟩)
-- `Iris.Algebra.WeakMonoidHomomorphism.map_op` idx 9: necessary (op₂ = constant 0 on AN: no left identity)
theorem w2c5_21 : ¬ indep0% Iris.Algebra.WeakMonoidHomomorphism.map_op 9 := fun H =>
  z_bad (@H AN AN _ _ addAN zAN ⟨0⟩ ⟨0⟩ anAdd Eq id ⟨0⟩ ⟨0⟩)
-- `Iris.Algebra.WeakMonoidHomomorphism.map_op` idx 12: necessary (R = False)
theorem w2c5_22 : ¬ drop0% Iris.Algebra.WeakMonoidHomomorphism.map_op 12 := fun H =>
  @H AN AN _ _ addAN addAN ⟨0⟩ ⟨0⟩ anAdd anAdd (fun _ _ => False) id ⟨0⟩ ⟨0⟩
-- `Iris.Algebra.MonoidHomomorphism.toWeakMonoidHomomorphism` idx 8: necessary (op₁ = constant 0 on AN: no left identity)
theorem w2c5_23 : ¬ indep0% Iris.Algebra.MonoidHomomorphism.toWeakMonoidHomomorphism 8 := fun H =>
  z_bad (@H AN AN _ _ zAN addAN ⟨0⟩ ⟨0⟩ anAdd Eq id)
-- `Iris.Algebra.MonoidHomomorphism.toWeakMonoidHomomorphism` idx 9: necessary (op₂ = constant 0 on AN: no left identity)
theorem w2c5_24 : ¬ indep0% Iris.Algebra.MonoidHomomorphism.toWeakMonoidHomomorphism 9 := fun H =>
  z_bad (@H AN AN _ _ addAN zAN ⟨0⟩ ⟨0⟩ anAdd Eq id)
-- `Iris.Algebra.MonoidHomomorphism.toWeakMonoidHomomorphism` idx 12: necessary (R = False is not reflexive)
theorem w2c5_25 : ¬ drop0% Iris.Algebra.MonoidHomomorphism.toWeakMonoidHomomorphism 12 := fun H =>
  (@H AN AN _ _ addAN addAN ⟨0⟩ ⟨0⟩ anAdd anAdd (fun _ _ => False) id).rel_refl (a := ⟨0⟩)
-- `Iris.Algebra.MonoidHomomorphism.map_unit` idx 8: necessary (op₁ = constant 0 on AN: no left identity)
theorem w2c5_26 : ¬ indep0% Iris.Algebra.MonoidHomomorphism.map_unit 8 := fun H =>
  z_bad (@H AN AN _ _ zAN addAN ⟨0⟩ ⟨0⟩ anAdd Eq id)
-- `Iris.Algebra.MonoidHomomorphism.map_unit` idx 9: necessary (op₂ = constant 0 on AN: no left identity)
theorem w2c5_27 : ¬ indep0% Iris.Algebra.MonoidHomomorphism.map_unit 9 := fun H =>
  z_bad (@H AN AN _ _ addAN zAN ⟨0⟩ ⟨0⟩ anAdd Eq id)
-- `Iris.Algebra.MonoidHomomorphism.map_unit` idx 12: necessary (R = False)
theorem w2c5_28 : ¬ drop0% Iris.Algebra.MonoidHomomorphism.map_unit 12 := fun H =>
  @H AN AN _ _ addAN addAN ⟨0⟩ ⟨0⟩ anAdd anAdd (fun _ _ => False) id

-- `Iris.Mra.sound` idx 4: necessary (R = Eq on Bool: mk [] ≠ mk [true])
theorem w2c5_29 : ¬ drop0% Iris.Mra.sound 4 := fun H =>
  nil_ne (@Eq Bool) true true rfl (@H Bool (@Eq Bool) [] [true])
-- `Iris.Mra.ind` idx 3: necessary (motive = False)
theorem w2c5_30 : ¬ drop0% Iris.Mra.ind 3 := fun H =>
  @H Bool (@Eq Bool) (fun _ => False) (Mra.mk [])
-- `Iris.Mra.ind₂` idx 3: necessary (motive = False)
theorem w2c5_31 : ¬ drop0% Iris.Mra.ind₂ 3 := fun H =>
  @H Bool (@Eq Bool) (fun _ _ => False) (Mra.mk []) (Mra.mk [])
-- `Iris.Mra.ind₃` idx 3: necessary (motive = False)
theorem w2c5_32 : ¬ drop0% Iris.Mra.ind₃ 3 := fun H =>
  @H Bool (@Eq Bool) (fun _ _ _ => False) (Mra.mk []) (Mra.mk []) (Mra.mk [])
-- `Iris.Mra.eq_of_below_iff` idx 4: necessary (R = Eq on Bool: mk [] ≠ toMra true)
theorem w2c5_33 : ¬ drop0% Iris.Mra.eq_of_below_iff 4 := fun H =>
  nil_ne (@Eq Bool) true true rfl (@H Bool (@Eq Bool) (Mra.mk []) (Mra.toMra true))
-- `Iris.Mra.toMra_op_of_rel` idx 5: necessary (R = Eq on Bool, a = false, b = true)
theorem w2c5_34 : ¬ drop0% Iris.Mra.toMra_op_of_rel 5 := fun H => by
  have e := @H Bool (@Eq Bool) inferInstance false true
  have hb : Mra.below false (Mra.toMra (R := @Eq Bool) false • Mra.toMra true) :=
    (Mra.below_op _ _ _).mpr (.inl ((Mra.below_toMra _ _).mpr rfl))
  rw [e] at hb
  exact absurd ((Mra.below_toMra _ _).mp hb) (by decide)
-- `Iris.Mra.toMra_ord_iff` idx 2: necessary (R = False on Unit: all toMra are the unit, so a ≼ₒ b but not R a b)
theorem w2c5_35 : ¬ drop0% Iris.Mra.toMra_ord_iff 2 := fun H =>
  (@H Unit (fun _ _ => False) ⟨fun h _ => h⟩ () ()).mp ((Mra.ord_iff _ _).mpr (Mra.idem _).symm)
-- `Iris.Mra.toMra_inc_iff` idx 2: necessary (R = False on Unit: a ≼ b but not R a b)
theorem w2c5_36 : ¬ drop0% Iris.Mra.toMra_inc_iff 2 := fun H =>
  (@H Unit (fun _ _ => False) ⟨fun h _ => h⟩ () ()).mp ((Mra.inc_iff _ _).mpr (Mra.idem _).symm)
-- `Iris.Mra.local_update_grow` idx 6: necessary (R = Eq on Bool, a = x-part false, b = true; frame z = toMra false)
theorem w2c5_37 : ¬ drop0% Iris.Mra.local_update_grow 6 := fun H => by
  have h := @H Bool (@Eq Bool) inferInstance false (Mra.toMra false) true
  have ⟨_, e⟩ := (local_update_unital_discrete _ _ _ _).mp h (Mra.toMra false) trivial (Mra.idem _).symm
  have hb : Mra.below false (Mra.toMra (R := @Eq Bool) true • Mra.toMra false) :=
    (Mra.below_op _ _ _).mpr (.inr ((Mra.below_toMra _ _).mpr rfl))
  rw [← e] at hb
  exact absurd ((Mra.below_toMra _ _).mp hb) (by decide)
-- `Iris.Mra.local_update_get_frag` idx 6: necessary (R = Eq on Bool, a = false, b = true; frame z = toMra false)
theorem w2c5_38 : ¬ drop0% Iris.Mra.local_update_get_frag 6 := fun H => by
  have h := @H Bool (@Eq Bool) ⟨fun _ => rfl⟩ inferInstance false true
  have ⟨_, e⟩ := (local_update_unital_discrete _ _ _ _).mp h (Mra.toMra false) trivial UORA.unit_left_id.symm
  have hb : Mra.below true (Mra.toMra (R := @Eq Bool) true • Mra.toMra false) :=
    (Mra.below_op _ _ _).mpr (.inl ((Mra.below_toMra _ _).mpr rfl))
  rw [← e] at hb
  exact absurd ((Mra.below_toMra _ _).mp hb) (by decide)
-- `Iris.Mra.toMra_rel_proper` idx 3: necessary (Bool, R = Eq, S = ≠: hrel holds, S irreflexive)
theorem w2c5_39 : ¬ drop0% Iris.Mra.toMra_rel_proper 3 := fun H =>
  toMra_ne (@Eq Bool) false true rfl (by decide)
    (@H Bool (@Eq Bool) (fun a b => a ≠ b) neq_hrel false true Bool.false_ne_true)
-- `Iris.Mra.toMra_rel_proper` idx 4: necessary (Bool, R = Eq, S = True)
theorem w2c5_40 : ¬ drop0% Iris.Mra.toMra_rel_proper 4 := fun H =>
  toMra_ne (@Eq Bool) false true rfl (by decide)
    (@H Bool (@Eq Bool) (fun _ _ => True) trivial false true trivial)
-- `Iris.Mra.toMra_rel_proper` idx 7: necessary (Bool, R = S = Eq; a = false, b = true)
theorem w2c5_41 : ¬ drop0% Iris.Mra.toMra_rel_proper 7 := fun H =>
  toMra_ne (@Eq Bool) false true rfl (by decide)
    (@H Bool (@Eq Bool) (@Eq Bool) rfl eq_hrel false true)
-- `Iris.Mra.toMra_injective` idx 2: necessary (Bool, R = False: antisymmetric vacuously, toMra constant)
theorem w2c5_42 : ¬ drop0% Iris.Mra.toMra_injective 2 := fun H =>
  absurd (@H Bool (fun _ _ => False) ⟨fun h _ => h.elim⟩ false true (toMra_eq_of fun _ => Iff.rfl))
    (by decide)
-- `Iris.Mra.toMra_injective` idx 3: necessary (Bool, R = True: reflexive, toMra constant)
theorem w2c5_43 : ¬ drop0% Iris.Mra.toMra_injective 3 := fun H =>
  absurd (@H Bool (fun _ _ => True) ⟨fun _ => trivial⟩ false true (toMra_eq_of fun _ => Iff.rfl))
    (by decide)
-- `Iris.Mra.toMra_proper` idx 3: necessary (Bool, ≈ is ≠, R = Eq)
theorem w2c5_44 : ¬ drop0% Iris.Mra.toMra_proper 3 := fun H =>
  toMra_ne (@Eq Bool) false true rfl (by decide)
    (@H Bool (@Eq Bool) ⟨fun a b => a ≠ b⟩ neq_hrel false true Bool.false_ne_true)
-- `Iris.Mra.toMra_proper` idx 4: necessary (Bool, ≈ is True, R = Eq)
theorem w2c5_45 : ¬ drop0% Iris.Mra.toMra_proper 4 := fun H =>
  toMra_ne (@Eq Bool) false true rfl (by decide)
    (@H Bool (@Eq Bool) ⟨fun _ _ => True⟩ ⟨fun _ => trivial⟩ false true trivial)
-- `Iris.Mra.toMra_proper` idx 7: necessary (Bool, ≈ and R both Eq; a = false, b = true)
theorem w2c5_46 : ¬ drop0% Iris.Mra.toMra_proper 7 := fun H =>
  toMra_ne (@Eq Bool) false true rfl (by decide)
    (@H Bool (@Eq Bool) ⟨fun a b => a = b⟩ ⟨fun _ => rfl⟩ eq_hrel false true)
-- `Iris.Mra.toMra_equiv_injective` idx 3: necessary (Bool, ≈ is Eq, R = False: toMra constant)
theorem w2c5_47 : ¬ drop0% Iris.Mra.toMra_equiv_injective 3 := fun H =>
  absurd (@H Bool (fun _ _ => False) ⟨fun a b => a = b⟩ ⟨fun h _ => h.elim⟩ false true
    (toMra_eq_of fun _ => Iff.rfl)) Bool.false_ne_true
-- `Iris.Mra.toMra_equiv_injective` idx 4: necessary (Bool, ≈ is Eq, R = True: toMra constant)
theorem w2c5_48 : ¬ drop0% Iris.Mra.toMra_equiv_injective 4 := fun H =>
  absurd (@H Bool (fun _ _ => True) ⟨fun a b => a = b⟩ ⟨fun _ => trivial⟩ false true
    (toMra_eq_of fun _ => Iff.rfl)) Bool.false_ne_true
-- `Iris.Mra.toMra_equiv_injective` idx 7: necessary (Bool, ≈ and R both Eq: false ≈ true fails)
theorem w2c5_49 : ¬ drop0% Iris.Mra.toMra_equiv_injective 7 := fun H =>
  absurd (@H Bool (@Eq Bool) ⟨fun a b => a = b⟩ ⟨fun _ => rfl⟩ ⟨fun h _ => h⟩ false true) Bool.false_ne_true
