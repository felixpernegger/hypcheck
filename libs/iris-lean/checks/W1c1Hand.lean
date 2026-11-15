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

namespace W1c1
open Iris Iris.Algebra Iris.Std

/-- Discrete OFE on Nat (Dist = Eq). -/
instance natOFE : OFE Nat := OFE.ofDiscrete Nat

theorem natNE2 (f : Nat → Nat → Nat) : OFE.NonExpansive₂ f :=
  ⟨fun n x₁ x₂ h y₁ y₂ h' => by
    change x₁ = x₂ at h; change y₁ = y₂ at h'; subst h h'; exact OFE.Dist.of_eq rfl⟩

/-- Addition on Nat, as a named operation. -/
def ad (a b : Nat) : Nat := a + b

/-- (Nat, +, 0) as a commutative monoid. -/
instance addMon : MonoidOps ad 0 where
  op_ne := natNE2 _
  op_assoc := Nat.add_assoc _ _ _
  op_comm := Nat.add_comm _ _
  op_left_id := Nat.zero_add _

/-- (Nat, max, 0) as a commutative monoid. -/
instance maxMon : MonoidOps (M := Nat) max 0 where
  op_ne := natNE2 _
  op_assoc := Nat.max_assoc _ _ _
  op_comm := Nat.max_comm _ _
  op_left_id := Nat.zero_max _

/-- Left projection (not commutative). -/
def lp (a _ : Nat) : Nat := a

/-- The left projection is not a commutative monoid operation. -/
theorem badMon : ¬ MonoidOps lp 0 := fun h =>
  absurd (@MonoidOps.op_comm _ _ _ _ h 0 1) (by decide)

abbrev TM (V : Type) := Std.ExtTreeMap Nat V compare



abbrev TMB (V : Type) := Std.ExtTreeMap Bool V compare
abbrev TMI (V : Type) := Std.ExtTreeMap Int V compare

/-- Finite sets of Bool as characteristic functions (copied from Probe4). -/
def BS := Bool → Bool

instance : Iris.Std.Set BS Bool where
  mem X x := X x = true
  singleton y := fun x => x == y
  union X Y := fun x => or (X x) (Y x)
  inter X Y := fun x => and (X x) (Y x)
  sdiff X Y := fun x => and (X x) (not (Y x))
  emptyCollection := fun _ => false

def bsList (X : BS) : List Bool := (if X false then [false] else []) ++ (if X true then [true] else [])

instance bsLFS : LawfulFiniteSet BS Bool where
  ext {X Y} h := funext fun x => by
    have := h x; cases hx : X x <;> cases hy : Y x <;> simp_all [Membership.mem]
  mem_empty := by intro x h; cases h
  mem_singleton := by intro x y; show (x == y) = true ↔ x = y; simp
  mem_union := by intro X Y x; show (or (X x) (Y x)) = true ↔ X x = true ∨ Y x = true; simp
  mem_inter := by intro X Y x; show (and (X x) (Y x)) = true ↔ X x = true ∧ Y x = true; simp
  mem_diff := by intro X Y x; show (and (X x) (not (Y x))) = true ↔ X x = true ∧ ¬ Y x = true; simp
  toList := bsList
  mem_toList := by
    intro m k; show k ∈ bsList m ↔ m k = true
    cases hf : m false <;> cases ht : m true <;> cases k <;> simp [bsList, hf, ht]
  toList_nodup := by
    intro m; cases hf : m false <;> cases ht : m true <;> simp [bsList, hf, ht]

theorem emptyDisj : PartialMap.disjoint (∅ : TM Nat) ∅ :=
  (PartialMap.disjoint_iff _ _).mpr fun k => .inl (get?_empty k)


open LawfulPartialMap in
/-- Map lookups in the empty map never succeed. -/
theorem emptyGet {V : Type} {k : Nat} {y : V} (e : get? (∅ : TM V) k = some y) : False := by
  rw [get?_empty] at e; cases e

abbrev sg {V : Type} (i : Nat) (x : V) : TM V := PartialMap.insert ∅ i x
abbrev tw {V : Type} (a b : V) : TM V := PartialMap.insert (PartialMap.insert ∅ 0 a) 1 b

theorem emp {V : Type} (Φ : Nat → V → Nat) : bigOpM ad Φ (∅ : TM V) = 0 := BigOpM.bigOpM_empty Φ

theorem sing {V : Type} (Φ : Nat → V → Nat) (i : Nat) (x : V) : bigOpM ad Φ (sg i x) = Φ i x := by
  rw [BigOpM.bigOpM_insert_eq (op := ad) Φ x (get?_empty i), BigOpM.bigOpM_empty]; rfl

theorem two {V : Type} (Φ : Nat → V → Nat) (a b : V) : bigOpM ad Φ (tw a b) = ad (Φ 1 b) (Φ 0 a) := by
  rw [BigOpM.bigOpM_insert_eq (op := ad) Φ b ((get?_insert_ne (by decide)).trans (get?_empty 1)), sing]

theorem insIns {V : Type} (a b : V) : PartialMap.insert (sg 0 a) 0 b = sg 0 b :=
  equiv_iff_eq.mp fun k => by
    by_cases hk : 0 = k
    · rw [get?_insert_eq hk, get?_insert_eq hk]
    · rw [get?_insert_ne hk, get?_insert_ne hk, get?_insert_ne hk]

open LawfulPartialMap in
theorem unionSelf {M' : Type → Type} {K V : Type} [LawfulPartialMap M' K] (m : M' V) : m ∪ m = m :=
  equiv_iff_eq.mp fun k => by
    rw [get?_union]; cases get? m k <;> rfl

open LawfulPartialMap in
theorem zw {A B C : Type} (f : A → B → C) (a : A) (b : B) :
    PartialMap.zipWith f (sg 0 a) (sg 0 b) = sg 0 (f a b) :=
  equiv_iff_eq.mp fun k => by
    rw [get?_zipWith]
    by_cases hk : 0 = k
    · rw [get?_insert_eq hk, get?_insert_eq hk, get?_insert_eq hk]; rfl
    · rw [get?_insert_ne hk, get?_insert_ne hk, get?_insert_ne hk, get?_empty, get?_empty, get?_empty]; rfl

theorem domSg {A B : Type} (a : A) (b : B) (k : Nat) :
    (get? (sg 0 a) k).isSome = true ↔ (get? (sg 0 b) k).isSome = true := by
  by_cases hk : 0 = k
  · rw [get?_insert_eq hk, get?_insert_eq hk]; rfl
  · rw [get?_insert_ne hk, get?_insert_ne hk, get?_empty, get?_empty]; exact Iff.rfl

open LawfulPartialMap in
theorem ofListU (L : List (Nat × Unit)) (hL : ∀ e ∈ L, e.1 = 0) (hne : L ≠ []) :
    (PartialMap.ofList L : TM Unit) = sg 0 () := by
  induction L with
  | nil => exact absurd rfl hne
  | cons e L ih =>
    obtain ⟨k, u⟩ := e
    have hk : k = 0 := hL _ (List.mem_cons_self ..)
    subst hk
    cases L with
    | nil => rfl
    | cons e' L' =>
      rw [ofList_cons, ih (fun e he => hL e (List.mem_cons_of_mem _ he)) (List.cons_ne_nil _ _), insIns]

/-- A weak monoid homomorphism (Nat,+,0) → (Nat,max,0) that does not preserve the unit: the constant 1. -/
theorem wh : @WeakMonoidHomomorphism Nat Nat _ _ ad max 0 0 addMon maxMon Eq (fun _ => 1) where
  rel_refl := rfl
  rel_trans := Eq.trans
  op_proper := fun e1 e2 => e1 ▸ e2 ▸ rfl
  map_ne := ⟨fun _ _ _ _ => OFE.Dist.of_eq rfl⟩
  map_op := rfl

end W1c1
open Iris Iris.Algebra Iris.Std W1c1

-- `Iris.Algebra.BigOpL.bigOpL_eq` (hypothesis 9): necessary, (Nat,+,0), l=[0], Φ=0, Ψ=1
theorem c1_1 : ¬ drop0% Iris.Algebra.BigOpL.bigOpL_eq 9 := fun h =>
  (by decide : ¬ (0:Nat) = 1) (@h Nat Nat _ ad 0 addMon (fun _ _ => 0) (fun _ _ => 1) [0])

-- `Iris.Algebra.BigOpL.bigOpL_dist` (hypothesis 10): necessary, discrete Nat, l=[0], Φ=0, Ψ=1
theorem c1_2 : ¬ drop0% Iris.Algebra.BigOpL.bigOpL_dist 10 := fun h =>
  (by decide : ¬ (0:Nat) = 1) (@h Nat Nat _ ad 0 addMon (fun _ _ => 0) (fun _ _ => 1) [0] 0)

-- `Iris.Algebra.BigOpL.bigOpL_eq_of_forall_eq` (hypothesis 9): necessary, l=[0], Φ=0, Ψ=1
theorem c1_3 : ¬ drop0% Iris.Algebra.BigOpL.bigOpL_eq_of_forall_eq 9 := fun h =>
  (by decide : ¬ (0:Nat) = 1) (@h Nat Nat _ ad 0 addMon (fun _ _ => 0) (fun _ _ => 1) [0])

-- `Iris.Algebra.BigOpL.bigOpL_closed` (hypothesis 9): necessary, P = False, l = []
theorem c1_4 : ¬ drop0% Iris.Algebra.BigOpL.bigOpL_closed 9 := fun h =>
  @h Nat Nat _ ad 0 addMon (fun _ => False) (fun _ _ => 0) [] (fun e _ => e) (fun e => by simp at e)

-- `Iris.Algebra.BigOpL.bigOpL_closed` (hypothesis 10): necessary, P x = x ≤ 1, Φ = 1, l = [0,0]: 1+1 = 2
theorem c1_5 : ¬ drop0% Iris.Algebra.BigOpL.bigOpL_closed 10 := fun h =>
  (by decide : ¬ (2:Nat) ≤ 1) (@h Nat Nat _ ad 0 addMon (fun x => x ≤ 1) (fun _ _ => 1) [0, 0] (Nat.zero_le 1) (fun _ => Nat.le_refl 1))

-- `Iris.Algebra.BigOpL.bigOpL_closed` (hypothesis 11): necessary, P x = (x = 0), Φ = 1, l = [0]
theorem c1_6 : ¬ drop0% Iris.Algebra.BigOpL.bigOpL_closed 11 := fun h =>
  (by decide : ¬ (1:Nat) = 0) (@h Nat Nat _ ad 0 addMon (fun x => x = 0) (fun _ _ => 1) [0] rfl
    (fun {x y} (e1 : x = 0) (e2 : y = 0) => by subst e1; subst e2; rfl))

-- `Iris.Algebra.BigOpL.bigOpL_eq_of_perm` (hypothesis 9): necessary, l₁ = [0], l₂ = [], Φ = 1
theorem c1_7 : ¬ drop0% Iris.Algebra.BigOpL.bigOpL_eq_of_perm 9 := fun h =>
  (by decide : ¬ (1:Nat) = 0) (@h Nat Nat _ ad 0 addMon (fun _ => 1) [0] [])

-- `Iris.Algebra.BigOpL.bigOpL_gen_proper_2` (hypothesis 12): necessary, R = False, empty lists
theorem c1_8 : ¬ drop0% Iris.Algebra.BigOpL.bigOpL_gen_proper_2 12 := fun h =>
  @h Nat Nat _ ad 0 addMon Nat (fun _ _ => False) (fun _ _ => 0) (fun _ _ => 0) [] [] (fun e _ => e) rfl
    (fun e _ => by simp at e)

-- `Iris.Algebra.BigOpL.bigOpL_gen_proper_2` (hypothesis 13): necessary, R a b = (a ≤ 1 ∧ b ≤ 1), Φ = Ψ = 1, lists [0,0]
theorem c1_9 : ¬ drop0% Iris.Algebra.BigOpL.bigOpL_gen_proper_2 13 := fun h =>
  (by decide : ¬ (2:Nat) ≤ 1) (And.left (@h Nat Nat _ ad 0 addMon Nat (fun a b => a ≤ 1 ∧ b ≤ 1) (fun _ _ => 1)
    (fun _ _ => 1) [0, 0] [0, 0] ⟨Nat.zero_le 1, Nat.zero_le 1⟩ rfl (fun _ _ => ⟨Nat.le_refl 1, Nat.le_refl 1⟩)))

-- `Iris.Algebra.BigOpL.bigOpL_gen_proper_2` (hypothesis 14): necessary, R = Eq, l₁ = [], l₂ = [0], Ψ = 1
theorem c1_10 : ¬ drop0% Iris.Algebra.BigOpL.bigOpL_gen_proper_2 14 := fun h =>
  (by decide : ¬ (0:Nat) = 1) (@h Nat Nat _ ad 0 addMon Nat Eq (fun _ _ => 1) (fun _ _ => 1) [] [0] rfl
    (fun e1 e2 => e1 ▸ e2 ▸ rfl) (fun e _ => by simp at e))

-- `Iris.Algebra.BigOpL.bigOpL_gen_proper_2` (hypothesis 15): necessary, R = Eq, l₁ = l₂ = [0], Φ = 0, Ψ = 1
theorem c1_11 : ¬ drop0% Iris.Algebra.BigOpL.bigOpL_gen_proper_2 15 := fun h =>
  (by decide : ¬ (0:Nat) = 1) (@h Nat Nat _ ad 0 addMon Nat Eq (fun _ _ => 0) (fun _ _ => 1) [0] [0] rfl
    (fun e1 e2 => e1 ▸ e2 ▸ rfl) rfl)

-- `Iris.Algebra.BigOpL.bigOpL_gen_proper` (hypothesis 10): necessary, R = False, l = []
theorem c1_12 : ¬ drop0% Iris.Algebra.BigOpL.bigOpL_gen_proper 10 := fun h =>
  @h Nat Nat _ ad 0 addMon (fun _ _ => False) (fun _ _ => 0) (fun _ _ => 0) [] (fun e _ => e) (fun e => by simp at e)

-- `Iris.Algebra.BigOpL.bigOpL_gen_proper` (hypothesis 11): necessary, R a b = (a = b ∨ a,b ≤ 1), Φ = 1, Ψ = 0, l = [0,0]
theorem c1_13 : ¬ drop0% Iris.Algebra.BigOpL.bigOpL_gen_proper 11 := fun h =>
  (by decide : ¬ ((2:Nat) = 0 ∨ ((2:Nat) ≤ 1 ∧ (0:Nat) ≤ 1))) (@h Nat Nat _ ad 0 addMon
    (fun a b => a = b ∨ (a ≤ 1 ∧ b ≤ 1)) (fun _ _ => 1) (fun _ _ => 0) [0, 0] (Or.inl rfl)
    (fun _ => Or.inr ⟨Nat.le_refl 1, Nat.zero_le 1⟩))

-- `Iris.Algebra.BigOpL.bigOpL_gen_proper` (hypothesis 12): necessary, R = Eq, l = [0], Φ = 0, Ψ = 1
theorem c1_14 : ¬ drop0% Iris.Algebra.BigOpL.bigOpL_gen_proper 12 := fun h =>
  (by decide : ¬ (0:Nat) = 1) (@h Nat Nat _ ad 0 addMon Eq (fun _ _ => 0) (fun _ _ => 1) [0] rfl
    (fun e1 e2 => e1 ▸ e2 ▸ rfl))

-- `Iris.Algebra.BigOpL.bigOpL_proper_2` (hypothesis 11): necessary, l₁ = [], l₂ = [0], Ψ = 1
theorem c1_15 : ¬ drop0% Iris.Algebra.BigOpL.bigOpL_proper_2 11 := fun h =>
  (by decide : ¬ (0:Nat) = 1) (@h Nat Nat _ ad 0 addMon _ (fun _ _ => 1) (fun _ _ => 1) [] [0] (fun e _ => by simp at e))

-- `Iris.Algebra.BigOpL.bigOpL_proper_2` (hypothesis 12): necessary, l₁ = l₂ = [0], Φ = 0, Ψ = 1
theorem c1_16 : ¬ drop0% Iris.Algebra.BigOpL.bigOpL_proper_2 12 := fun h =>
  (by decide : ¬ (0:Nat) = 1) (@h Nat Nat _ ad 0 addMon _ (fun _ _ => 0) (fun _ _ => 1) [0] [0] rfl)

-- `Iris.Algebra.BigOpL.bigOpL_zipWith_op_eq` (hypothesis 15): necessary, f x y = y, g1 = 0, g2 = id, l₁ = [1], l₂ = [0], Φ k x = x, Ψ = 0
theorem c1_17 : ¬ drop0% Iris.Algebra.BigOpL.bigOpL_zipWith_op_eq 15 := fun h =>
  (by decide : ¬ (0:Nat) = 1) (@h Nat Nat _ ad 0 addMon Nat Nat (fun _ y => y) (fun _ => 0) id [1] [0]
    (fun _ x => x) (fun _ _ => 0) rfl rfl)

-- `Iris.Algebra.BigOpL.bigOpL_zipWith_op_eq` (hypothesis 16): necessary, f x y = x, g1 = id, g2 = 0, l₁ = [0], l₂ = [1], Φ = 0, Ψ k y = y
theorem c1_18 : ¬ drop0% Iris.Algebra.BigOpL.bigOpL_zipWith_op_eq 16 := fun h =>
  (by decide : ¬ (0:Nat) = 1) (@h Nat Nat _ ad 0 addMon Nat Nat (fun x _ => x) id (fun _ => 0) [0] [1]
    (fun _ _ => 0) (fun _ y => y) rfl rfl)

-- `Iris.Algebra.BigOpL.bigOpL_zip_op_eq` (hypothesis 11): necessary, l₁ = [1], l₂ = [], Φ k x = x: zip is empty
theorem c1_19 : ¬ drop0% Iris.Algebra.BigOpL.bigOpL_zip_op_eq 11 := fun h =>
  (by decide : ¬ (0:Nat) = 1) (@h Nat Nat _ ad 0 addMon Nat [1] [] (fun _ x => x) (fun _ _ => 0))

-- `Iris.Algebra.BigOpL.bigOpL_hom` (hypothesis 13): necessary, R = False, l = []
theorem c1_20 : ¬ drop0% Iris.Algebra.BigOpL.bigOpL_hom 13 := fun h =>
  @h Nat Nat _ _ ad ad 0 0 addMon addMon Nat (fun _ _ => False) id (fun _ _ => 0) []

-- `Iris.Algebra.BigOpL.bigOpL_hom_weak` (hypothesis 13): necessary, R = False, l = [0]
theorem c1_21 : ¬ drop0% Iris.Algebra.BigOpL.bigOpL_hom_weak 13 := fun h =>
  @h Nat Nat _ _ ad ad 0 0 addMon addMon Nat (fun _ _ => False) id [0] (fun _ _ => 0) (List.cons_ne_nil 0 [])

-- `Iris.Algebra.BigOpL.bigOpL_hom_weak` (hypothesis 16): necessary, f = const 1 from (Nat,+,0) to (Nat,max,0) is a weak hom; l = [] gives 1 = 0
theorem c1_22 : ¬ drop0% Iris.Algebra.BigOpL.bigOpL_hom_weak 16 := fun h =>
  (by decide : ¬ (1:Nat) = 0) (@h Nat Nat _ _ ad max 0 0 addMon maxMon Nat Eq (fun _ => 1) wh [] (fun _ _ => 0))

-- `Iris.Algebra.BigOpM.bigOpM_eq_of_perm` (hypothesis 12): necessary, m₁ = ∅, m₂ = {0 ↦ 0}, Φ = 1
theorem c1_23 : ¬ drop0% Iris.Algebra.BigOpM.bigOpM_eq_of_perm 12 := fun h => by
  have := @h Nat _ ad 0 addMon TM Nat Nat _ (fun _ _ => 1) ∅ (sg 0 0)
  rw [emp, sing] at this; exact absurd this (by decide)

-- `Iris.Algebra.BigOpM.bigOpM_insert_eq` (hypothesis 13): necessary, m = {0 ↦ 0}, i = 0, Φ = 1: 1 vs 2
theorem c1_24 : ¬ drop0% Iris.Algebra.BigOpM.bigOpM_insert_eq 13 := fun h => by
  have := @h Nat _ ad 0 addMon TM Nat Nat _ (fun _ _ => 1) (sg 0 0) 0 0
  rw [insIns] at this; repeat rw [sing] at this; exact absurd this (by decide)

-- `Iris.Algebra.BigOpM.bigOpM_gen_proper_2` (hypothesis 17): necessary, R a b = (a ≤ 1 ↔ b ≤ 1) (an equivalence, not a congruence), m = {0 ↦ 0, 1 ↦ 0}, Φ = 1, Ψ = 0
theorem c1_25 : ¬ drop0% Iris.Algebra.BigOpM.bigOpM_gen_proper_2 17 := fun h => by
  have := @h Nat _ ad 0 addMon TM Nat _ Nat Nat (fun a b => (a ≤ 1 ↔ b ≤ 1)) (fun _ _ => 1) (fun _ _ => 0)
    (tw 0 0) (tw 0 0) (fun e => by subst e; exact Iff.rfl) ⟨fun _ => Iff.rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩
    (fun _ => rfl) (fun _ _ => iff_of_true (Nat.le_refl 1) (Nat.zero_le 1))
  rw [two, two] at this; exact (by decide : ¬ (ad 1 1 ≤ 1 ↔ ad 0 0 ≤ 1)) this

-- `Iris.Algebra.BigOpM.bigOpM_gen_proper_2` (hypothesis 18): necessary, R = Eq, m1 = ∅, m2 = {0 ↦ 0}, Ψ = 1
theorem c1_26 : ¬ drop0% Iris.Algebra.BigOpM.bigOpM_gen_proper_2 18 := fun h => by
  have := @h Nat _ ad 0 addMon TM Nat _ Nat Nat Eq (fun _ _ => 1) (fun _ _ => 1) ∅ (sg 0 0) id
    ⟨Eq.refl, Eq.symm, Eq.trans⟩ (fun e1 e2 => e1 ▸ e2 ▸ rfl) (fun e _ => (emptyGet e).elim)
  rw [emp, sing] at this; exact absurd this (by decide)

-- `Iris.Algebra.BigOpM.bigOpM_gen_proper_2` (hypothesis 19): necessary, R = Eq, m1 = m2 = {0 ↦ 0}, Φ = 0, Ψ = 1
theorem c1_27 : ¬ drop0% Iris.Algebra.BigOpM.bigOpM_gen_proper_2 19 := fun h => by
  have := @h Nat _ ad 0 addMon TM Nat _ Nat Nat Eq (fun _ _ => 0) (fun _ _ => 1) (sg 0 0) (sg 0 0) id
    ⟨Eq.refl, Eq.symm, Eq.trans⟩ (fun e1 e2 => e1 ▸ e2 ▸ rfl) (fun _ => rfl)
  repeat rw [sing] at this; exact absurd this (by decide)

-- `Iris.Algebra.BigOpM.bigOpM_gen_proper` (hypothesis 13): necessary, R = False, m = ∅
theorem c1_28 : ¬ drop0% Iris.Algebra.BigOpM.bigOpM_gen_proper 13 := fun h =>
  @h Nat _ ad 0 addMon TM Nat Nat _ (fun _ _ => False) (fun _ _ => 0) (fun _ _ => 0) ∅ (fun e _ => e)
    (fun e => (emptyGet e).elim)

-- `Iris.Algebra.BigOpM.bigOpM_gen_proper` (hypothesis 14): necessary, R a b = (a = b ∨ a,b ≤ 1), m = {0 ↦ 0, 1 ↦ 0}, Φ = 1, Ψ = 0
theorem c1_29 : ¬ drop0% Iris.Algebra.BigOpM.bigOpM_gen_proper 14 := fun h => by
  have := @h Nat _ ad 0 addMon TM Nat Nat _ (fun a b => a = b ∨ (a ≤ 1 ∧ b ≤ 1)) (fun _ _ => 1) (fun _ _ => 0)
    (tw 0 0) (Or.inl rfl) (fun _ => Or.inr ⟨Nat.le_refl 1, Nat.zero_le 1⟩)
  rw [two, two] at this; exact (by decide : ¬ (ad 1 1 = ad 0 0 ∨ (ad 1 1 ≤ 1 ∧ ad 0 0 ≤ 1))) this

-- `Iris.Algebra.BigOpM.bigOpM_gen_proper` (hypothesis 15): necessary, R = Eq, m = {0 ↦ 0}, Φ = 0, Ψ = 1
theorem c1_30 : ¬ drop0% Iris.Algebra.BigOpM.bigOpM_gen_proper 15 := fun h => by
  have := @h Nat _ ad 0 addMon TM Nat Nat _ Eq (fun _ _ => 0) (fun _ _ => 1) (sg 0 0) rfl (fun e1 e2 => e1 ▸ e2 ▸ rfl)
  repeat rw [sing] at this; exact absurd this (by decide)

-- `Iris.Algebra.BigOpM.bigOpM_dist` (hypothesis 13): necessary, discrete Nat, m = {0 ↦ 0}, Φ = 0, Ψ = 1
theorem c1_31 : ¬ drop0% Iris.Algebra.BigOpM.bigOpM_dist 13 := fun h => by
  have := @h Nat _ ad 0 addMon TM Nat Nat _ 0 (fun _ _ => 0) (fun _ _ => 1) (sg 0 0)
  repeat rw [sing] at this; exact (by decide : ¬ (0:Nat) = 1) this

-- `Iris.Algebra.BigOpM.bigOpM_eq` (hypothesis 12): necessary, m = {0 ↦ 0}, Φ = 0, Ψ = 1
theorem c1_32 : ¬ drop0% Iris.Algebra.BigOpM.bigOpM_eq 12 := fun h => by
  have := @h Nat _ ad 0 addMon TM Nat Nat _ (fun _ _ => 0) (fun _ _ => 1) (sg 0 0)
  repeat rw [sing] at this; exact absurd this (by decide)

-- `Iris.Algebra.BigOpM.bigOpM_eq_strong` (hypothesis 14): necessary, m1 = ∅, m2 = {0 ↦ 0}, Φ = Ψ = 1
theorem c1_33 : ¬ drop0% Iris.Algebra.BigOpM.bigOpM_eq_strong 14 := fun h => by
  have := @h Nat _ ad 0 addMon TM Nat _ Nat _ (fun _ _ => 1) (fun _ _ => 1) ∅ (sg 0 0) (fun e _ _ => (emptyGet e).elim)
  rw [emp, sing] at this; exact absurd this (by decide)

-- `Iris.Algebra.BigOpM.bigOpM_eq_strong` (hypothesis 15): necessary, m1 = m2 = {0 ↦ 0}, Φ = 0, Ψ = 1
theorem c1_34 : ¬ drop0% Iris.Algebra.BigOpM.bigOpM_eq_strong 15 := fun h => by
  have := @h Nat _ ad 0 addMon TM Nat _ Nat _ (fun _ _ => 0) (fun _ _ => 1) (sg 0 0) (sg 0 0) (fun _ => rfl)
  repeat rw [sing] at this; exact absurd this (by decide)

-- `Iris.Algebra.BigOpM.bigOpM_dist_pointwise` (hypothesis 13): necessary, m = {0 ↦ 0}, Φ = 0, Ψ = 1
theorem c1_35 : ¬ drop0% Iris.Algebra.BigOpM.bigOpM_dist_pointwise 13 := fun h => by
  have := @h Nat _ ad 0 addMon TM Nat Nat _ (fun _ _ => 0) (fun _ _ => 1) 0 (sg 0 0)
  repeat rw [sing] at this; exact (by decide : ¬ (0:Nat) = 1) this

-- `Iris.Algebra.BigOpM.bigOpM_eq_of_forall_eq` (hypothesis 12): necessary, m = {0 ↦ 0}, Φ = 0, Ψ = 1
theorem c1_36 : ¬ drop0% Iris.Algebra.BigOpM.bigOpM_eq_of_forall_eq 12 := fun h => by
  have := @h Nat _ ad 0 addMon TM Nat Nat _ (fun _ _ => 0) (fun _ _ => 1) (sg 0 0)
  repeat rw [sing] at this; exact absurd this (by decide)

-- `Iris.Algebra.BigOpM.bigOpM_ofList_eq` (hypothesis 12): necessary, l = [(0,0),(0,0)] (duplicate key), Φ = 1: 1 vs 2
theorem c1_37 : ¬ drop0% Iris.Algebra.BigOpM.bigOpM_ofList_eq 12 := fun h => by
  have := @h Nat _ ad 0 addMon TM Nat Nat _ _ (fun _ _ => 1) [(0, 0), (0, 0)]
  rw [show (PartialMap.ofList [(0, 0), (0, 0)] : TM Nat) = PartialMap.insert (sg 0 0) 0 0 from rfl, insIns, sing] at this
  exact absurd this (by decide)

-- `Iris.Algebra.BigOpM.bigOpM_insert_override_eq` (hypothesis 15): necessary, m = {0 ↦ 0}, x' = 1, Φ k v = v
theorem c1_38 : ¬ drop0% Iris.Algebra.BigOpM.bigOpM_insert_override_eq 15 := fun h => by
  have := @h Nat _ ad 0 addMon TM Nat _ Nat 0 0 1 (fun _ v => v) (sg 0 0) (get?_insert_eq rfl)
  rw [insIns] at this; repeat rw [sing] at this; exact absurd this (by decide)

-- `Iris.Algebra.BigOpM.bigOpM_fn_insert_eq` (hypothesis 17): necessary, m = {0 ↦ 0}, i = 0, g = 1: 1 vs 2
theorem c1_39 : ¬ drop0% Iris.Algebra.BigOpM.bigOpM_fn_insert_eq 17 := fun h => by
  have := @h Nat _ ad 0 addMon TM Nat Nat _ _ Nat (fun _ _ _ => 1) (fun _ => 0) (sg 0 0) 0 0 0
  rw [insIns] at this; repeat rw [sing] at this; exact absurd this (by decide)

-- `Iris.Algebra.BigOpM.bigOpM_fn_insert_eq'` (hypothesis 15): necessary, m = {0 ↦ 0}, i = 0, f = 1, P = 1: 1 vs 2
theorem c1_40 : ¬ drop0% Iris.Algebra.BigOpM.bigOpM_fn_insert_eq' 15 := fun h => by
  have := @h Nat _ ad 0 addMon TM Nat Nat _ _ (fun _ => 1) (sg 0 0) 0 0 1
  rw [insIns] at this; repeat rw [sing] at this; exact absurd this (by decide)

-- `Iris.Algebra.BigOpM.toList_union_perm` (hypothesis 7): necessary, m1 = m2 = {0 ↦ 0}: lists of length 1 and 2
theorem c1_41 : ¬ drop0% Iris.Algebra.BigOpM.toList_union_perm 7 := fun h => by
  have p := @h TM Nat Nat _ _ (sg 0 0) (sg 0 0)
  rw [unionSelf] at p
  have e1 := BigOpL.bigOpL_eq_of_perm (op := ad) (fun _ => (1:Nat)) p
  rw [BigOpL.bigOpL_append_eq] at e1
  change bigOpM ad (fun _ _ => 1) (sg 0 0) =
    ad (bigOpM ad (fun _ _ => 1) (sg 0 0)) (bigOpM ad (fun _ _ => 1) (sg 0 0)) at e1
  rw [sing] at e1; exact absurd e1 (by decide)

-- `Iris.Algebra.BigOpM.bigOpM_union_eq` (hypothesis 13): necessary, m1 = m2 = {0 ↦ 0}, Φ = 1: 1 vs 2
theorem c1_42 : ¬ drop0% Iris.Algebra.BigOpM.bigOpM_union_eq 13 := fun h => by
  have := @h Nat _ ad 0 addMon TM Nat Nat _ _ (fun _ _ => 1) (sg 0 0) (sg 0 0)
  rw [unionSelf, sing] at this; exact absurd this (by decide)

-- `Iris.Algebra.BigOpM.bigOpM_closed` (hypothesis 12): necessary, P = False, m = ∅
theorem c1_43 : ¬ drop0% Iris.Algebra.BigOpM.bigOpM_closed 12 := fun h =>
  @h Nat _ ad 0 addMon TM Nat Nat _ (fun _ => False) (fun _ _ => 0) ∅ (fun e _ => e) (fun e => (emptyGet e).elim)

-- `Iris.Algebra.BigOpM.bigOpM_closed` (hypothesis 13): necessary, P x = x ≤ 1, Φ = 1, m = {0 ↦ 0, 1 ↦ 0}
theorem c1_44 : ¬ drop0% Iris.Algebra.BigOpM.bigOpM_closed 13 := fun h => by
  have := @h Nat _ ad 0 addMon TM Nat Nat _ (fun x => x ≤ 1) (fun _ _ => 1) (tw 0 0) (Nat.zero_le 1) (fun _ => Nat.le_refl 1)
  rw [two] at this; exact (by decide : ¬ ad 1 1 ≤ 1) this

-- `Iris.Algebra.BigOpM.bigOpM_closed` (hypothesis 14): necessary, P x = (x = 0), Φ = 1, m = {0 ↦ 0}
theorem c1_45 : ¬ drop0% Iris.Algebra.BigOpM.bigOpM_closed 14 := fun h => by
  have := @h Nat _ ad 0 addMon TM Nat Nat _ (fun x => x = 0) (fun _ _ => 1) (sg 0 0) rfl
    (fun {x y} (e1 : x = 0) (e2 : y = 0) => by subst e1; subst e2; rfl)
  rw [sing] at this; exact (by decide : ¬ (1:Nat) = 0) this

-- `Iris.Algebra.BigOpM.bigOpM_kmap_eq` (hypothesis 14): necessary, f = const 0 (not injective), m = {0 ↦ (), 1 ↦ ()}, Φ = 1: 1 vs 2
theorem c1_46 : ¬ drop0% Iris.Algebra.BigOpM.bigOpM_kmap_eq 14 := fun h => by
  have := @h Nat _ ad 0 addMon TM Nat Unit _ Nat TM _ _ (fun _ => 0) (fun _ _ => 1) (tw () ())
  have hk : (FiniteMap.kmap (fun _ => 0) (tw () ()) : TM Unit) = sg 0 () := by
    refine ofListU _ (fun e he => ?_) (fun hnil => ?_)
    · obtain ⟨kv, _, rfl⟩ := List.mem_map.mp he; rfl
    · have hm : ((1 : Nat), ()) ∈ toList (tw () ()) := (toList_get (M := TM) (K := Nat)).mpr (get?_insert_eq rfl)
      rw [List.map_eq_nil_iff] at hnil; rw [hnil] at hm; cases hm
  rw [hk, sing, two] at this; exact absurd this (by decide)

-- `Iris.Algebra.BigOpM.bigOpM_sep_zipWith_eq` (hypothesis 18): necessary, f x y = y, g1 = 0, g2 = id, m1 = {0 ↦ 1}, m2 = {0 ↦ 0}, h1 k x = x, h2 = 0
theorem c1_47 : ¬ drop0% Iris.Algebra.BigOpM.bigOpM_sep_zipWith_eq 18 := fun h => by
  have := @h Nat _ ad 0 addMon TM Nat _ Nat Nat Nat (fun _ y => y) (fun _ => 0) id (fun _ x => x) (fun _ _ => 0)
    (sg 0 1) (sg 0 0) rfl (domSg 1 0)
  rw [zw] at this; repeat rw [sing] at this; exact absurd this (by decide)

-- `Iris.Algebra.BigOpM.bigOpM_sep_zipWith_eq` (hypothesis 19): necessary, f x y = x, g1 = id, g2 = 0, m1 = {0 ↦ 0}, m2 = {0 ↦ 1}, h1 = 0, h2 k y = y
theorem c1_48 : ¬ drop0% Iris.Algebra.BigOpM.bigOpM_sep_zipWith_eq 19 := fun h => by
  have := @h Nat _ ad 0 addMon TM Nat _ Nat Nat Nat (fun x _ => x) id (fun _ => 0) (fun _ _ => 0) (fun _ y => y)
    (sg 0 0) (sg 0 1) rfl (domSg 0 1)
  rw [zw] at this; repeat rw [sing] at this; exact absurd this (by decide)

-- `Iris.Algebra.BigOpL.bigOpL_closed` (hypothesis 5): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i1 : ¬ indep0% Iris.Algebra.BigOpL.bigOpL_closed 5 := fun h =>
  badMon (h (M := Nat) (A := Nat) (op := lp) (unit := 0) (P := fun _ => True) (Φ := fun _ _ => 0) (l := []) trivial (fun _ _ => trivial) (fun _ => trivial))

-- `Iris.Algebra.BigOpL.bigOpL_gen_proper_2` (hypothesis 5): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i2 : ¬ indep0% Iris.Algebra.BigOpL.bigOpL_gen_proper_2 5 := fun h =>
  badMon (h (M := Nat) (A := Nat) (op := lp) (unit := 0) (B := Nat) (R := fun _ _ => True) (Φ := fun _ _ => 0) (Ψ := fun _ _ => 0) (l₁ := []) (l₂ := []) trivial (fun _ _ => trivial) rfl (fun _ _ => trivial))

-- `Iris.Algebra.BigOpL.bigOpL_gen_proper` (hypothesis 5): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i3 : ¬ indep0% Iris.Algebra.BigOpL.bigOpL_gen_proper 5 := fun h =>
  badMon (h (M := Nat) (A := Nat) (op := lp) (unit := 0) (R := fun _ _ => True) (Φ := fun _ _ => 0) (Ψ := fun _ _ => 0) (l := []) trivial (fun _ _ => trivial) (fun _ => trivial))

-- `Iris.Algebra.BigOpL.bigOpL_zipWith_op_eq` (hypothesis 5): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i4 : ¬ indep0% Iris.Algebra.BigOpL.bigOpL_zipWith_op_eq 5 := fun h =>
  badMon (h (M := Nat) (A := Nat) (op := lp) (unit := 0) (B := Nat) (C := Nat × Nat) (f := Prod.mk) (g1 := Prod.fst) (g2 := Prod.snd) (l₁ := []) (l₂ := []) (Φ := fun _ _ => 0) (Ψ := fun _ _ => 0) rfl rfl rfl)

-- `Iris.Algebra.BigOpL.bigOpL_comm_map` (hypothesis 5): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i5 : ¬ indep0% Iris.Algebra.BigOpL.bigOpL_comm_map 5 := fun h =>
  badMon (h (M := Nat) (A := Nat) (op := lp) (unit := 0) (B := Nat) (K := Nat) (M' := TM) (Φ := fun _ _ _ _ => 0) (l := []) (m := ∅))

-- `Iris.Algebra.BigOpL.bigOpL_comm_set` (hypothesis 5): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i6 : ¬ indep0% Iris.Algebra.BigOpL.bigOpL_comm_set 5 := fun h =>
  badMon (h (M := Nat) (A := Nat) (op := lp) (unit := 0) (B := Bool) (S := BS) (Φ := fun _ _ _ => 0) (l := []) (s := ∅))

-- `Iris.Algebra.BigOpL.bigOpL_comm_mset` (hypothesis 5): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i7 : ¬ indep0% Iris.Algebra.BigOpL.bigOpL_comm_mset 5 := fun h =>
  badMon (h (M := Nat) (A := Nat) (op := lp) (unit := 0) (B := Nat) (MS := ListPerm Nat) (Φ := fun _ _ _ => 0) (l := []) (X := ∅))

-- `Iris.Algebra.BigOpL.bigOpL_hom` (hypothesis 8): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i8 : ¬ indep0% Iris.Algebra.BigOpL.bigOpL_hom 8 := fun h =>
  badMon (@h Nat Nat _ _ lp ad 0 0 addMon Nat Eq id (fun _ _ => 0) [])

-- `Iris.Algebra.BigOpL.bigOpL_hom` (hypothesis 9): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i9 : ¬ indep0% Iris.Algebra.BigOpL.bigOpL_hom 9 := fun h =>
  badMon (@h Nat Nat _ _ ad lp 0 0 addMon Nat Eq id (fun _ _ => 0) [])

-- `Iris.Algebra.BigOpL.bigOpL_hom_weak` (hypothesis 9): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i10 : ¬ indep0% Iris.Algebra.BigOpL.bigOpL_hom_weak 9 := fun h =>
  badMon (@h Nat Nat _ _ ad lp 0 0 addMon Nat Eq id [0] (fun _ _ => 0) (List.cons_ne_nil 0 []))

-- `Iris.Algebra.BigOpM.bigOpM_eq_of_perm` (hypothesis 4): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i11 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_eq_of_perm 4 := fun h =>
  badMon (h (M := Nat) (op := lp) (unit := 0) (M' := TM) (K := Nat) (V := Nat) (Φ := fun _ _ => 0) (m₁ := ∅) (m₂ := ∅) (fun _ => rfl))

-- `Iris.Algebra.BigOpM.bigOpM_empty` (hypothesis 4): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i12 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_empty 4 := fun h =>
  badMon (h (M := Nat) (op := lp) (unit := 0) (M' := TM) (K := Nat) (V := Nat) (Φ := fun _ _ => 0))

-- `Iris.Algebra.BigOpM.bigOpM_insert_eq` (hypothesis 4): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i13 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_insert_eq 4 := fun h =>
  badMon (h (M := Nat) (op := lp) (unit := 0) (M' := TM) (K := Nat) (V := Nat) (Φ := fun _ _ => 0) (m := ∅) (i := 0) (x := 0) (get?_empty 0))

-- `Iris.Algebra.BigOpM.bigOpM_delete_eq` (hypothesis 4): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i14 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_delete_eq 4 := fun h =>
  badMon (h (M := Nat) (op := lp) (unit := 0) (M' := TM) (K := Nat) (V := Nat) (Φ := fun _ _ => 0) (m := PartialMap.insert ∅ 0 0) (i := 0) (x := 0) (get?_insert_eq rfl))

-- `Iris.Algebra.BigOpM.bigOpM_gen_proper_2` (hypothesis 4): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i15 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_gen_proper_2 4 := fun h =>
  badMon (h (M := Nat) (op := lp) (unit := 0) (M' := TM) (K := Nat) (A := Nat) (B := Nat) (R := fun _ _ => True) (Φ := fun _ _ => 0) (Ψ := fun _ _ => 0) (m1 := ∅) (m2 := ∅) (fun _ => trivial) ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩ (fun _ _ => trivial) (fun _ => rfl) (fun _ _ => trivial))

-- `Iris.Algebra.BigOpM.bigOpM_gen_proper` (hypothesis 4): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i16 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_gen_proper 4 := fun h =>
  badMon (h (M := Nat) (op := lp) (unit := 0) (M' := TM) (K := Nat) (V := Nat) (R := fun _ _ => True) (Φ := fun _ _ => 0) (Ψ := fun _ _ => 0) (m := ∅) trivial (fun _ _ => trivial) (fun _ => trivial))

-- `Iris.Algebra.BigOpM.bigOpM_dist` (hypothesis 4): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i17 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_dist 4 := fun h =>
  badMon (h (M := Nat) (op := lp) (unit := 0) (M' := TM) (K := Nat) (V := Nat) (n := 0) (Φ := fun _ _ => 0) (Ψ := fun _ _ => 0) (m := ∅) (fun _ => OFE.Dist.of_eq rfl))

-- `Iris.Algebra.BigOpM.bigOpM_eq` (hypothesis 4): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i18 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_eq 4 := fun h =>
  badMon (h (M := Nat) (op := lp) (unit := 0) (M' := TM) (K := Nat) (V := Nat) (Φ := fun _ _ => 0) (Ψ := fun _ _ => 0) (m := ∅) (fun _ => rfl))

-- `Iris.Algebra.BigOpM.bigOpM_eq_strong` (hypothesis 4): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i19 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_eq_strong 4 := fun h =>
  badMon (h (M := Nat) (op := lp) (unit := 0) (M' := TM) (K := Nat) (A := Nat) (Φ := fun _ _ => 0) (Ψ := fun _ _ => 0) (m1 := ∅) (m2 := ∅) (fun _ => rfl) (fun _ _ _ => rfl))

-- `Iris.Algebra.BigOpM.bigOpM_dist_pointwise` (hypothesis 4): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i20 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_dist_pointwise 4 := fun h =>
  badMon (h (M := Nat) (op := lp) (unit := 0) (M' := TM) (K := Nat) (V := Nat) (Φ := fun _ _ => 0) (Ψ := fun _ _ => 0) (n := 0) (m := ∅) (OFE.Dist.of_eq rfl))

-- `Iris.Algebra.BigOpM.bigOpM_eq_of_forall_eq` (hypothesis 4): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i21 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_eq_of_forall_eq 4 := fun h =>
  badMon (h (M := Nat) (op := lp) (unit := 0) (M' := TM) (K := Nat) (V := Nat) (Φ := fun _ _ => 0) (Ψ := fun _ _ => 0) (m := ∅) rfl)

-- `Iris.Algebra.BigOpM.bigOpM_toList_eq` (hypothesis 4): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i22 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_toList_eq 4 := fun h =>
  badMon (h (M := Nat) (op := lp) (unit := 0) (M' := TM) (K := Nat) (V := Nat) (Φ := fun _ _ => 0) (m := ∅))

-- `Iris.Algebra.BigOpM.bigOpM_ofList_eq` (hypothesis 4): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i23 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_ofList_eq 4 := fun h =>
  badMon (h (M := Nat) (op := lp) (unit := 0) (M' := TM) (K := Nat) (V := Nat) (Φ := fun _ _ => 0) (l := []) List.nodup_nil)

-- `Iris.Algebra.BigOpM.bigOpM_singleton_eq` (hypothesis 4): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i24 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_singleton_eq 4 := fun h =>
  badMon (h (M := Nat) (op := lp) (unit := 0) (M' := TM) (K := Nat) (V := Nat) (Φ := fun _ _ => 0) (i := 0) (x := 0))

-- `Iris.Algebra.BigOpM.bigOpM_const_unit_eq` (hypothesis 4): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i25 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_const_unit_eq 4 := fun h =>
  badMon (h (M := Nat) (op := lp) (unit := 0) (M' := TM) (K := Nat) (V := Nat) (m := ∅))

-- `Iris.Algebra.BigOpM.bigOpM_map_eq` (hypothesis 4): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i26 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_map_eq 4 := fun h =>
  badMon (h (M := Nat) (op := lp) (unit := 0) (M' := TM) (K := Nat) (V := Nat) (B := Nat) (h := id) (Φ := fun _ _ => 0) (m := ∅))

-- `Iris.Algebra.BigOpM.bigOpM_filterMap_eq` (hypothesis 4): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i27 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_filterMap_eq 4 := fun h =>
  badMon (h (M := Nat) (op := lp) (unit := 0) (M' := TM) (K := Nat) (V := Nat) (h := some) (Φ := fun _ _ => 0) (m := ∅) (fun _ _ e => Option.some.inj e))

-- `Iris.Algebra.BigOpM.bigOpM_insert_delete_eq` (hypothesis 4): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i28 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_insert_delete_eq 4 := fun h =>
  badMon (h (M := Nat) (op := lp) (unit := 0) (M' := TM) (K := Nat) (V := Nat) (Φ := fun _ _ => 0) (m := ∅) (i := 0) (x := 0))

-- `Iris.Algebra.BigOpM.bigOpM_insert_override_eq` (hypothesis 4): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i29 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_insert_override_eq 4 := fun h =>
  badMon (h (M := Nat) (op := lp) (unit := 0) (M' := TM) (K := Nat) (A := Nat) (i := 0) (x := 0) (x' := 0) (Φ := fun _ _ => 0) (m := PartialMap.insert ∅ 0 0) (get?_insert_eq rfl) rfl)

-- `Iris.Algebra.BigOpM.bigOpM_fn_insert_eq` (hypothesis 4): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i30 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_fn_insert_eq 4 := fun h =>
  badMon (h (M := Nat) (op := lp) (unit := 0) (M' := TM) (K := Nat) (V := Nat) (B := Nat) (g := fun _ _ _ => 0) (f := fun _ => 0) (m := ∅) (i := 0) (x := 0) (b := 0) (get?_empty 0))

-- `Iris.Algebra.BigOpM.bigOpM_fn_insert_eq'` (hypothesis 4): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i31 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_fn_insert_eq' 4 := fun h =>
  badMon (h (M := Nat) (op := lp) (unit := 0) (M' := TM) (K := Nat) (V := Nat) (f := fun _ => 0) (m := ∅) (i := 0) (x := 0) (P := 0) (get?_empty 0))

-- `Iris.Algebra.BigOpM.bigOpM_filter_eq` (hypothesis 4): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i32 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_filter_eq 4 := fun h =>
  badMon (h (M := Nat) (op := lp) (unit := 0) (M' := TM) (K := Nat) (V := Nat) (φ := fun _ _ => true) (Φ := fun _ _ => 0) (m := ∅))

-- `Iris.Algebra.BigOpM.bigOpM_union_eq` (hypothesis 4): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i33 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_union_eq 4 := fun h =>
  badMon (h (M := Nat) (op := lp) (unit := 0) (M' := TM) (K := Nat) (V := Nat) (Φ := fun _ _ => 0) (m1 := ∅) (m2 := ∅) emptyDisj)

-- `Iris.Algebra.BigOpM.bigOpM_closed` (hypothesis 4): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i34 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_closed 4 := fun h =>
  badMon (h (M := Nat) (op := lp) (unit := 0) (M' := TM) (K := Nat) (V := Nat) (P := fun _ => True) (Φ := fun _ _ => 0) (m := ∅) trivial (fun _ _ => trivial) (fun _ => trivial))

-- `Iris.Algebra.BigOpM.bigOpM_kmap_eq` (hypothesis 4): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i35 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_kmap_eq 4 := fun h =>
  badMon (h (M := Nat) (op := lp) (unit := 0) (M' := TM) (K := Nat) (V := Nat) (K' := Nat) (M'' := TM) (f := id) (fun _ _ e => e) (Φ := fun _ _ => 0) (m := ∅))

-- `Iris.Algebra.BigOpM.bigOpM_map_seq_eq` (hypothesis 4): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i36 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_map_seq_eq 4 := fun h =>
  badMon (h (M := Nat) (op := lp) (unit := 0) (V := Nat) (M'' := TM) (Φ := fun _ _ => 0) (start := 0) (l := []))

-- `Iris.Algebra.BigOpM.bigOpM_map_seqZ_eq` (hypothesis 4): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i37 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_map_seqZ_eq 4 := fun h =>
  badMon (h (M := Nat) (op := lp) (unit := 0) (V := Nat) (M'' := TMI) (Φ := fun _ _ => 0) (start := 0) (l := []))

-- `Iris.Algebra.BigOpM.bigOpM_dom_set_eq` (hypothesis 4): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i38 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_dom_set_eq 4 := fun h =>
  badMon (h (M := Nat) (op := lp) (unit := 0) (M' := TMB) (K := Bool) (V := Nat) (S := BS) (Φ := fun _ => 0) (m := ∅))

-- `Iris.Algebra.BigOpM.bigOpM_ofSetWith_eq` (hypothesis 4): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i39 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_ofSetWith_eq 4 := fun h =>
  badMon (h (M := Nat) (op := lp) (unit := 0) (M' := TMB) (K := Bool) (V := Nat) (S := BS) (Φ := fun _ _ => 0) (g := fun _ => 0) (s := ∅))

-- `Iris.Algebra.BigOpM.bigOpM_ofSet_eq` (hypothesis 4): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i40 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_ofSet_eq 4 := fun h =>
  badMon (h (M := Nat) (op := lp) (unit := 0) (M' := TMB) (K := Bool) (V := Nat) (S := BS) (Φ := fun _ _ => 0) (s := ∅) (c := 0))

-- `Iris.Algebra.BigOpM.bigOpM_sep_zipWith_eq` (hypothesis 4): necessary, left projection on Nat is not a commutative monoid (op 0 1 = 0, op 1 0 = 1)
theorem c1_i41 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_sep_zipWith_eq 4 := fun h =>
  badMon (h (M := Nat) (op := lp) (unit := 0) (M' := TM) (K := Nat) (A := Nat) (B := Nat) (C := Nat × Nat) (f := Prod.mk) (g1 := Prod.fst) (g2 := Prod.snd) (h1 := fun _ _ => 0) (h2 := fun _ _ => 0) (m1 := ∅) (m2 := ∅) rfl rfl (fun _ => Iff.rfl))

-- `Iris.Algebra.BigOpM.bigOpM_gen_proper_2` (hypothesis 15): removable, derivable: hR_sub follows from reflexivity in hR_eqv
theorem c1_r1 : drop% Iris.Algebra.BigOpM.bigOpM_gen_proper_2 15 := by
  intro M _ op unit _ M' K _ A B R Φ Ψ m1 m2 hR_eqv hR_op hdom hf
  exact BigOpM.bigOpM_gen_proper_2 (fun h => h ▸ hR_eqv.refl _) hR_eqv hR_op hdom hf

-- `Iris.Algebra.BigOpM.bigOpM_gen_proper_2` (hypothesis 16): removable, the library proof uses transitivity only to chain the equalities given by hR_sub; rewriting them instead needs no Equivalence
theorem c1_r2 : drop% Iris.Algebra.BigOpM.bigOpM_gen_proper_2 16 := by
  intro M _ op unit _ M' K _ A B R Φ Ψ m1 m2 hR_sub hR_op hdom hf
  classical
  let P : M' A → Prop := fun m1' =>
    ∀ (m2' : M' B),
    (∀ k, (get? m1' k).isSome = (get? m2' k).isSome) →
    (∀ {k y1 y2}, get? m1' k = some y1 → get? m2' k = some y2 → R (Φ k y1) (Ψ k y2)) →
    R (bigOpM op (fun k x => Φ k x) m1') (bigOpM op (fun k x => Ψ k x) m2')
  suffices h : P m1 from h m2 hdom hf
  apply LawfulFiniteMap.induction_on (P := P)
  · intro m2' hdom' _
    rw [BigOpM.bigOpM_empty]
    refine hR_sub <| ((BigOpM.bigOpM_eq_of_perm Ψ fun k => ?_).trans (BigOpM.bigOpM_empty Ψ)).symm
    simpa [get?_empty] using hdom' k
  · intro k x1 m1' hm1'k IH m2' hdom' hf'
    obtain ⟨x2, hm2k⟩ := Option.isSome_iff_exists.mp <| by
      simpa [get?_insert_eq (k := k) rfl] using (hdom' k).symm
    rw [BigOpM.bigOpM_insert_eq Φ x1 hm1'k, BigOpM.bigOpM_delete_eq Ψ hm2k]
    exact hR_op (hf' (get?_insert_eq rfl) hm2k) <| IH _ (fun k' => by
      by_cases hkk' : k = k'
      · subst hkk'; simp [get?_delete_eq rfl, hm1'k]
      · rw [get?_delete_ne hkk']; simpa [get?_insert_ne hkk'] using hdom' k')
      (fun {k' _ _} h1' h2' => by
        have hkk' : k ≠ k' := fun h => by subst h; rw [hm1'k] at h1'; cases h1'
        exact hf' (by rwa [get?_insert_ne hkk']) (by rwa [get?_delete_ne hkk'] at h2'))

-- `Iris.Algebra.BigOpM.bigOpM_filterMap_eq` (hypothesis 12): removable, keys of a map are distinct, so injectivity of h is not needed; induction on m
theorem c1_r3 : drop% Iris.Algebra.BigOpM.bigOpM_filterMap_eq 12 := by
  intro M _ op unit _ M' K V _ h Φ m
  classical
  refine LawfulFiniteMap.induction_on (P := fun m => bigOpM op (fun k x => Φ k x) (PartialMap.filterMap h m) =
    bigOpM op (fun k v => (h v).elim unit (Φ k)) m) ?_ ?_ m
  · have e : PartialMap.filterMap h (∅ : M' V) = ∅ :=
      equiv_iff_eq.mp fun k => by rw [LawfulPartialMap.get?_filterMap, get?_empty]; rfl
    show bigOpM op (fun k x => Φ k x) (PartialMap.filterMap h (∅ : M' V)) = _
    rw [e, BigOpM.bigOpM_empty, BigOpM.bigOpM_empty]
  · intro i x m hi ih
    show bigOpM op (fun k x => Φ k x) (PartialMap.filterMap h (PartialMap.insert m i x)) = _
    rw [BigOpM.bigOpM_insert_eq _ x hi]
    cases hx : h x with
    | none =>
      have e : PartialMap.filterMap h (PartialMap.insert m i x) = PartialMap.filterMap h m :=
        equiv_iff_eq.mp fun k => by
          rw [LawfulPartialMap.get?_filterMap, LawfulPartialMap.get?_filterMap]
          by_cases hk : i = k
          · subst hk; rw [get?_insert_eq rfl, hi]; simp [hx]
          · rw [get?_insert_ne hk]
      rw [e, ih]; exact MonoidOps.op_left_id.symm
    | some w =>
      have e : PartialMap.filterMap h (PartialMap.insert m i x) =
          PartialMap.insert (PartialMap.filterMap h m) i w :=
        equiv_iff_eq.mp fun k => by
          by_cases hk : i = k
          · subst hk; rw [LawfulPartialMap.get?_filterMap, get?_insert_eq rfl, get?_insert_eq rfl]; simp [hx]
          · rw [LawfulPartialMap.get?_filterMap, get?_insert_ne hk, get?_insert_ne hk,
              LawfulPartialMap.get?_filterMap]
      have hi' : get? (PartialMap.filterMap h m) i = none := by
        rw [LawfulPartialMap.get?_filterMap, hi]; rfl
      rw [e, BigOpM.bigOpM_insert_eq _ w hi', ih]; rfl
