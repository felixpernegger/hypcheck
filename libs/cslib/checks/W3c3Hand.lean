import Lean.Elab.Command
import Cslib
-- CSLib toolkit header (copy of hypcheck runs/hand22/Header.lean with `import Cslib`; ~150 MB, 1.5 s to import)


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

namespace W3c3
open Relation

theorem rtgInv {α : Type} {r : α → α → Prop} (P : α → Prop) (hP : ∀ a b, r a b → P a → P b)
    {a b : α} (h : ReflTransGen r a b) (ha : P a) : P b := by
  induction h with
  | refl => exact ha
  | tail _ hbc ih => exact hP _ _ hbc ih

def R3 : ℕ → ℕ → Prop := fun a b => (a = 1 ∧ b = 0) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) ∨ (a = 2 ∧ b = 3)

theorem R3lc : LocallyConfluent R3 := by
  have p20 : ReflTransGen R3 2 0 := .head (show R3 2 1 by simp [R3]) (.single (show R3 1 0 by simp [R3]))
  have p13 : ReflTransGen R3 1 3 := .head (show R3 1 2 by simp [R3]) (.single (show R3 2 3 by simp [R3]))
  intro a b c hb hc
  simp only [R3] at hb hc
  rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  rcases hc with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> (try omega) <;>
  first
  | exact ⟨_, .refl, .refl⟩
  | exact ⟨0, .refl, p20⟩ | exact ⟨0, p20, .refl⟩
  | exact ⟨3, .refl, p13⟩ | exact ⟨3, p13, .refl⟩

theorem R3nc : ¬ Confluent R3 := fun h => by
  obtain ⟨d, h1, h2⟩ := h (a := 1) (b := 0) (c := 3) (.single (by simp [R3]))
    (.head (show R3 1 2 by simp [R3]) (.single (show R3 2 3 by simp [R3])))
  have a := rtgInv (fun c => c = 0) (by intro a b hab ha; simp [R3] at hab; omega) h1 rfl
  have b := rtgInv (fun c => c = 3) (by intro a b hab ha; simp [R3] at hab; omega) h2 rfl
  omega

/-- 0 → 1, 0 → 2 -/
def R5 : ℕ → ℕ → Prop := fun a b => a = 0 ∧ (b = 1 ∨ b = 2)
/-- 0 → 1 -/
def A : ℕ → ℕ → Prop := fun a b => a = 0 ∧ b = 1
/-- 0 → 2 -/
def B : ℕ → ℕ → Prop := fun a b => a = 0 ∧ b = 2
def E : ℕ → ℕ → Prop := fun _ _ => False
def U : Unit → Unit → Prop := fun _ _ => True

theorem termM {α : Type} {r : α → α → Prop} (f : α → ℕ) (hf : ∀ a b, r a b → f b < f a) :
    Terminating r := Subrelation.wf (fun {a b} h => hf b a h) (measure f).wf

theorem R5join12 : ¬ Join (ReflTransGen R5) 1 2 := fun ⟨d, h1, h2⟩ => by
  have a := rtgInv (fun c => c = 1) (by intro a b hab ha; simp [R5] at hab; omega) h1 rfl
  have b := rtgInv (fun c => c = 2) (by intro a b hab ha; simp [R5] at hab; omega) h2 rfl
  omega

theorem R5nc : ¬ Confluent R5 := fun h =>
  R5join12 (h (a := 0) (.single (by simp [R5])) (.single (by simp [R5])))

theorem R5nlc : ¬ LocallyConfluent R5 := fun h =>
  R5join12 (h (a := 0) (by simp [R5]) (by simp [R5]))

theorem R5term : Terminating R5 := termM (fun n => 3 - n) (by intro a b h; simp [R5] at h; omega)

theorem ABnc : ¬ Commute A B := fun h => by
  obtain ⟨d, h1, h2⟩ := h (x := 0) (y₁ := 1) (y₂ := 2) (.single (by simp [A])) (.single (by simp [B]))
  have a := rtgInv (fun c => c = 1) (by intro a b hab ha; simp [B] at hab; omega) h1 rfl
  have b := rtgInv (fun c => c = 2) (by intro a b hab ha; simp [A] at hab; omega) h2 rfl
  omega

theorem rtgMono {r p : ℕ → ℕ → Prop} (hrp : ∀ a b, r a b → p a b) {a b : ℕ}
    (h : ReflTransGen r a b) : ReflTransGen p a b := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.tail (hrp _ _ hbc)

theorem rtgE {a b : ℕ} (h : ReflTransGen E a b) : b = a :=
  rtgInv (fun c => c = a) (by intro _ _ h; exact h.elim) h rfl

theorem rtgSupE {r : ℕ → ℕ → Prop} {a b : ℕ} (h : ReflTransGen (r ⊔ E) a b) : ReflTransGen r a b :=
  rtgMono (fun x y h => h.elim id False.elim) h

theorem rtgESup {r : ℕ → ℕ → Prop} {a b : ℕ} (h : ReflTransGen (E ⊔ r) a b) : ReflTransGen r a b :=
  rtgMono (fun x y h => h.elim False.elim id) h

theorem commEr (r : ℕ → ℕ → Prop) : Commute E r := fun h1 h2 => by
  cases rtgE h1; exact ⟨_, h2, .refl⟩

theorem commrE (r : ℕ → ℕ → Prop) : Commute r E := fun h1 h2 => by
  cases rtgE h2; exact ⟨_, .refl, h1⟩

theorem confE : Confluent E := RightUnique.to_confluent (fun _ _ _ h => h.elim)
theorem confA : Confluent A := RightUnique.to_confluent (fun _ _ _ h1 h2 => by simp [A] at h1 h2; omega)
theorem confB : Confluent B := RightUnique.to_confluent (fun _ _ _ h1 h2 => by simp [B] at h1 h2; omega)
theorem crA : ChurchRosser A := confluent_iff_churchRosser.mp confA
theorem crE : ChurchRosser E := confluent_iff_churchRosser.mp confE

theorem notSNU' (x : Unit) : ¬ SN U x := fun h => by
  induction h with
  | intro x _ ih => exact ih () trivial

theorem notSNU : ¬ SN U () := notSNU' ()

theorem notTermU : ¬ Terminating U := fun h => notSNU (h.apply ())

theorem confU : Confluent U := fun _ _ => ⟨(), .refl, .refl⟩

end W3c3

namespace W3c3
open Relation





theorem risE {a b n : ℕ} (h : RelatesInSteps E a b n) : b = a := rtgE h.reflTransGen

/-- right Euclidean, not transitive: 0 → 1, and the clique {1, 2} -/
def RE : ℕ → ℕ → Prop := fun a b => (a = 0 ∧ b = 1) ∨ (1 ≤ a ∧ a ≤ 2 ∧ 1 ≤ b ∧ b ≤ 2)
/-- left Euclidean, not transitive: converse of RE -/
def LE' : ℕ → ℕ → Prop := fun a b => RE b a
/-- negation on Bool -/
def Ng : Bool → Bool → Prop := fun a b => b = !a

instance reRE : RightEuclidean RE := ⟨fun h1 h2 => by simp only [RE] at *; omega⟩
instance leLE : LeftEuclidean LE' := ⟨fun h1 h2 => by simp only [LE', RE] at *; omega⟩
theorem reNT : ¬ IsTrans ℕ RE := fun h => by
  have := h.trans 0 1 2 (by simp [RE]) (by simp [RE]); simp [RE] at this
theorem leNT : ¬ IsTrans ℕ LE' := fun h => by
  have := h.trans 2 1 0 (by simp [LE', RE]) (by simp [LE', RE]); simp [LE', RE] at this
theorem reNLE : ¬ LeftEuclidean RE := fun h => by
  have := h.leftEuclidean (a := 1) (b := 0) (c := 1) (by simp [RE]) (by simp [RE]); simp [RE] at this
theorem leNRE : ¬ RightEuclidean LE' := fun h => by
  have := h.rightEuclidean (a := 1) (b := 0) (c := 1) (by simp [LE', RE]) (by simp [LE', RE]); simp [LE', RE] at this
theorem aNRE : ¬ RightEuclidean A := fun h => by
  have := h.rightEuclidean (a := 0) (b := 1) (c := 1) (by simp [A]) (by simp [A]); simp [A] at this
theorem aNLE : ¬ LeftEuclidean A := fun h => by
  have := h.leftEuclidean (a := 0) (b := 0) (c := 1) (by simp [A]) (by simp [A]); simp [A] at this
instance aT : IsTrans ℕ A := ⟨fun a b c h1 h2 => by simp only [A] at *; omega⟩
theorem ngNT : ¬ IsTrans Bool Ng := fun h => by
  have := h.trans true false true rfl rfl; exact absurd (show true = !true from this) (by decide)
theorem ngRU : Relator.RightUnique Ng := fun a b c h1 h2 => by simp only [Ng] at *; rw [h1, h2]
theorem ngLU : Relator.LeftUnique Ng := fun a b c h1 h2 => by simp only [Ng] at *; revert h1 h2; cases a <;> cases b <;> cases c <;> decide
theorem ngLT : Relator.LeftTotal Ng := fun a => ⟨!a, rfl⟩
theorem ngRT : Relator.RightTotal Ng := fun b => ⟨!b, by simp [Ng]⟩

/-- `IsEquiv` restricted to dom: 0 → 0, 1 → 1, 0 → 2, 1 → 2 -/
def RD : ℕ → ℕ → Prop := fun a b => a ≤ 1 ∧ (b = a ∨ b = 2)
instance rdEq : IsEquiv ↑(Relation.dom RD) fun a b => RD ↑a ↑b where
  refl := fun x => by obtain ⟨b, hb⟩ := x.2; exact ⟨hb.1, Or.inl rfl⟩
  trans := fun x y z h1 h2 => by simp only [RD] at h1 h2 ⊢; omega
  symm := fun x y h1 => by obtain ⟨b, hb⟩ := y.2; simp only [RD] at hb h1 ⊢; omega

end W3c3

open W3c3 Relation


-- `Relation.DiamondCommute.diamond_commute_reflTransGen_right` idx 3: necessary (r₁ = 0→1, r₂ = 0→2)
theorem c0 : ¬ drop0% Relation.DiamondCommute.diamond_commute_reflTransGen_right 3 := fun h => by
  obtain ⟨d, h1, h2⟩ := (h (r₁ := A) (r₂ := B)) (show A 0 1 by simp [A]) (show ReflTransGen B 0 2 from .single (by simp [B]))
  simp [A] at h2

-- `Relation.DiamondCommute.diamond_commute_reflTransGen_left` idx 3: necessary (r₁ = 0→1, r₂ = 0→2)
theorem c1 : ¬ drop0% Relation.DiamondCommute.diamond_commute_reflTransGen_left 3 := fun h => by
  obtain ⟨d, h1, h2⟩ := (h (r₁ := A) (r₂ := B)) (show ReflTransGen A 0 1 from .single (by simp [A])) (show B 0 2 by simp [B])
  simp [B] at h1

-- `Relation.DiamondCommute.to_semiCommute` idx 3: necessary (r₁ = 0→1, r₂ = 0→2)
theorem c2 : ¬ drop0% Relation.DiamondCommute.to_semiCommute 3 := fun h =>
  ABnc (semiCommute_iff_commute.mp (h (r₁ := A) (r₂ := B)))

-- `Relation.Diamond.to_semiConfluent` idx 2: necessary (0→1, 0→2)
theorem c3 : ¬ drop0% Relation.Diamond.to_semiConfluent 2 := fun h =>
  R5nc (confluent_iff_semiConfluent.mpr (h (r := R5)))

-- `Relation.Diamond.extend` idx 2: necessary (0→1, 0→2)
theorem c4 : ¬ drop0% Relation.Diamond.extend 2 := fun h =>
  R5nc (confluent_iff_semiConfluent.mpr (h (r := R5)))

-- `Relation.Confluent.isTrans_join_reflTransGen` idx 2: necessary (0→1, 0→2)
theorem c5 : ¬ drop0% Relation.Confluent.isTrans_join_reflTransGen 2 := fun h =>
  R5join12 ((h (r := R5)).trans 1 0 2 ⟨1, .refl, .single (by simp [R5])⟩ ⟨2, .single (by simp [R5]), .refl⟩)

-- `Relation.SemiCommute.to_commute` idx 3: necessary (r₁ = 0→1, r₂ = 0→2)
theorem c6 : ¬ drop0% Relation.SemiCommute.to_commute 3 := fun h => ABnc (h (r₁ := A) (r₂ := B))

-- `Relation.SemiConfluent.to_confluent` idx 2: necessary (0→1, 0→2)
theorem c7 : ¬ drop0% Relation.SemiConfluent.to_confluent 2 := fun h => R5nc (h (r := R5))

-- `Relation.SemiConfluent.toConfluent` idx 2: necessary (0→1, 0→2)
theorem c8 : ¬ drop0% Relation.SemiConfluent.toConfluent 2 := fun h => R5nc (h (r := R5))

-- `Relation.DiamondCommute.to_commute` idx 3: necessary (r₁ = 0→1, r₂ = 0→2)
theorem c9 : ¬ drop0% Relation.DiamondCommute.to_commute 3 := fun h => ABnc (h (r₁ := A) (r₂ := B))

-- `Relation.Confluent.to_churchRosser` idx 2: necessary (0→1, 0→2)
theorem c10 : ¬ drop0% Relation.Confluent.to_churchRosser 2 := fun h =>
  R5nc (confluent_iff_churchRosser.mpr (h (r := R5)))

-- `Relation.Diamond.to_confluent` idx 2: necessary (0→1, 0→2)
theorem c11 : ¬ drop0% Relation.Diamond.to_confluent 2 := fun h => R5nc (h (r := R5))

-- `Relation.Diamond.toConfluent` idx 2: necessary (0→1, 0→2)
theorem c12 : ¬ drop0% Relation.Diamond.toConfluent 2 := fun h => R5nc (h (r := R5))

-- `Relation.confluent_of_unique_end` idx 3: necessary (0→1, 0→2)
theorem c13 : ¬ drop0% Relation.confluent_of_unique_end 3 := fun h => R5nc (h (r := R5) (x := 0))

-- `Relation.Confluent_of_unique_end` idx 3: necessary (0→1, 0→2)
theorem c14 : ¬ drop0% Relation.Confluent_of_unique_end 3 := fun h => R5nc (h (r := R5) (x := 0))

-- `Relation.ChurchRosser.normal_eqvGen_reflTransGen` idx 4: necessary (0→1, 0→2; y = 2, x = 1)
theorem c15 : ¬ drop0% Relation.ChurchRosser.normal_eqvGen_reflTransGen 4 := fun h => by
  have := h (r := R5) (x := 1) (y := 2) (by rintro ⟨z, hz⟩; simp [R5] at hz)
    (.trans 2 0 1 (.symm 0 2 (.rel 0 2 (by simp [R5]))) (.rel 0 1 (by simp [R5])))
  have := rtgInv (fun c => c = 2) (by intro a b hab ha; simp [R5] at hab; omega) this rfl
  omega

-- `Relation.ChurchRosser.normal_eqvGen_reflTransGen` idx 5: necessary (0→1; y = 1, x = 0)
theorem c16 : ¬ drop0% Relation.ChurchRosser.normal_eqvGen_reflTransGen 5 := fun h => by
  have := h (r := A) (x := 0) (y := 1) crA (.symm _ _ (.rel _ _ (by simp [A])))
  have := rtgInv (fun c => c = 1) (by intro a b hab ha; simp [A] at hab; omega) this rfl
  omega

-- `Relation.ChurchRosser.normal_eqvGen_reflTransGen` idx 6: necessary (empty relation, y = 1, x = 0)
theorem c17 : ¬ drop0% Relation.ChurchRosser.normal_eqvGen_reflTransGen 6 := fun h => by
  have := rtgE (h (r := E) (x := 0) (y := 1) crE (fun ⟨_, h⟩ => h))
  omega

-- `Relation.ChurchRosser.normal_eq` idx 4: necessary (0→1, 0→2; x = 1, y = 2)
theorem c18 : ¬ drop0% Relation.ChurchRosser.normal_eq 4 := fun h => by
  have := h (r := R5) (x := 1) (y := 2) (by rintro ⟨z, hz⟩; simp [R5] at hz) (by rintro ⟨z, hz⟩; simp [R5] at hz)
    (.trans 1 0 2 (.symm 0 1 (.rel 0 1 (by simp [R5]))) (.rel 0 2 (by simp [R5])))
  omega

-- `Relation.ChurchRosser.normal_eq` idx 5: necessary (0→1; x = 0, y = 1)
theorem c19 : ¬ drop0% Relation.ChurchRosser.normal_eq 5 := fun h => by
  have := h (r := A) (x := 0) (y := 1) crA (by rintro ⟨z, hz⟩; simp [A] at hz) (.rel _ _ (by simp [A]))
  omega

-- `Relation.ChurchRosser.normal_eq` idx 6: necessary (0→1; x = 1, y = 0)
theorem c20 : ¬ drop0% Relation.ChurchRosser.normal_eq 6 := fun h => by
  have := h (r := A) (x := 1) (y := 0) crA (by rintro ⟨z, hz⟩; simp [A] at hz) (.symm _ _ (.rel _ _ (by simp [A])))
  omega

-- `Relation.ChurchRosser.normal_eq` idx 7: necessary (empty relation, x = 0, y = 1)
theorem c21 : ¬ drop0% Relation.ChurchRosser.normal_eq 7 := fun h => by
  have := h (r := E) (x := 0) (y := 1) crE (fun ⟨_, h⟩ => h) (fun ⟨_, h⟩ => h)
  omega

-- `Relation.Confluent.equivalence_join_reflTransGen` idx 2: necessary (0→1, 0→2)
theorem c22 : ¬ drop0% Relation.Confluent.equivalence_join_reflTransGen 2 := fun h =>
  R5join12 ((h (r := R5)).trans (y := 0) ⟨1, .refl, .single (by simp [R5])⟩ ⟨2, .single (by simp [R5]), .refl⟩)

-- `Relation.Normalizing.confluent_iff_forall_unique_normal` idx 2: necessary (full relation on Unit)
theorem c23 : ¬ drop0% Relation.Normalizing.confluent_iff_forall_unique_normal 2 := fun h => by
  obtain ⟨n, ⟨_, hn⟩, _⟩ := (h (r := U)).mp confU ()
  exact hn ⟨(), trivial⟩

-- `Relation.Terminating.confluent_iff_forall_unique_normal` idx 2: necessary (full relation on Unit)
theorem c24 : ¬ drop0% Relation.Terminating.confluent_iff_forall_unique_normal 2 := fun h => by
  obtain ⟨n, ⟨_, hn⟩, _⟩ := (h (r := U)).mp confU ()
  exact hn ⟨(), trivial⟩

-- `Relation.Terminating.isConfluent_iff_all_unique_Normal` idx 2: necessary (full relation on Unit)
theorem c25 : ¬ drop0% Relation.Terminating.isConfluent_iff_all_unique_Normal 2 := fun h => by
  obtain ⟨n, ⟨_, hn⟩, _⟩ := (h (r := U)).mp confU ()
  exact hn ⟨(), trivial⟩

-- `Relation.Convergent.to_confluent` idx 2: necessary (0→1, 0→2)
theorem c26 : ¬ drop0% Relation.Convergent.to_confluent 2 := fun h => R5nc (h (r := R5))

-- `Relation.Convergent.isConfluent` idx 2: necessary (0→1, 0→2)
theorem c27 : ¬ drop0% Relation.Convergent.isConfluent 2 := fun h => R5nc (h (r := R5))

-- `Relation.Confluent.to_locallyConfluent` idx 2: necessary (0→1, 0→2)
theorem c28 : ¬ drop0% Relation.Confluent.to_locallyConfluent 2 := fun h => R5nlc (h (r := R5))

-- `Relation.Confluent.toLocallyConfluent` idx 2: necessary (0→1, 0→2)
theorem c29 : ¬ drop0% Relation.Confluent.toLocallyConfluent 2 := fun h => R5nlc (h (r := R5))

-- `Relation.LocallyCommute.commute_of_terminating_sup` idx 3: necessary (r₁ = 0→1, r₂ = 0→2)
theorem c30 : ¬ drop0% Relation.LocallyCommute.commute_of_terminating_sup 3 := fun h =>
  ABnc (h (r₁ := A) (r₂ := B) (termM (fun n => 3 - n) (by intro a b h; rcases h with h | h <;> simp [A, B] at h <;> omega)))

-- `Relation.LocallyCommute.commute_of_terminating_sup` idx 4: necessary (r₁ = r₂ = 0←1⇄2→3)
theorem c31 : ¬ drop0% Relation.LocallyCommute.commute_of_terminating_sup 4 := fun h =>
  R3nc (h (r₁ := R3) (r₂ := R3) R3lc)

-- `Relation.LocallyConfluent.terminating_toConfluent` idx 2: necessary (0→1, 0→2)
theorem c32 : ¬ drop0% Relation.LocallyConfluent.terminating_toConfluent 2 := fun h => R5nc (h (r := R5) R5term)

-- `Relation.LocallyConfluent.Terminating_toConfluent` idx 2: necessary (0→1, 0→2)
theorem c33 : ¬ drop0% Relation.LocallyConfluent.Terminating_toConfluent 2 := fun h => R5nc (h (r := R5) R5term)

-- `Relation.StronglyCommute.extend` idx 6: necessary (r₁ = 0→1, r₂ = 0→2, x = 0)
theorem c34 : ¬ drop0% Relation.StronglyCommute.extend 6 := fun h => by
  obtain ⟨w, h1, h2⟩ := h (r₁ := A) (r₂ := B) (x := 0) (y := 1) (z := 2) (.single (by simp [A])) (by simp [B])
  have b := rtgInv (fun c => c = 2) (by intro a b hab ha; simp [A] at hab; omega) h2 rfl
  subst b
  cases h1 with
  | single h => simp [B] at h

-- `Relation.StronglyCommute.extend` idx 7: necessary (r₁ empty, r₂ = 0→1, x = 0, y = 5)
theorem c35 : ¬ drop0% Relation.StronglyCommute.extend 7 := fun h => by
  obtain ⟨w, h1, h2⟩ := h (r₁ := E) (r₂ := A) (x := 0) (y := 5) (z := 1) (fun h _ => h.elim) (by simp [A])
  cases rtgE h2
  cases h1 with
  | single h => simp [A] at h

-- `Relation.StronglyCommute.to_commute` idx 3: necessary (r₁ = 0→1, r₂ = 0→2)
theorem c36 : ¬ drop0% Relation.StronglyCommute.to_commute 3 := fun h => ABnc (h (r₁ := A) (r₂ := B))

-- `Relation.StronglyCommute.toCommute` idx 3: necessary (r₁ = 0→1, r₂ = 0→2)
theorem c37 : ¬ drop0% Relation.StronglyCommute.toCommute 3 := fun h => ABnc (h (r₁ := A) (r₂ := B))

-- `Relation.DiamondCommute.join_left` idx 4: necessary (r₁ = 0→1, r₂ empty, r₃ = 0→2)
theorem c38 : ¬ drop0% Relation.DiamondCommute.join_left 4 := fun h => by
  obtain ⟨d, h1, h2⟩ := (h (r₁ := A) (r₂ := E) (r₃ := B) (fun h _ => h.elim))
    (show (A ⊔ E) 0 1 from Or.inl (by simp [A])) (show B 0 2 by simp [B])
  simp [B] at h1

-- `Relation.DiamondCommute.join_left` idx 5: necessary (r₁ empty, r₂ = 0→1, r₃ = 0→2)
theorem c39 : ¬ drop0% Relation.DiamondCommute.join_left 5 := fun h => by
  obtain ⟨d, h1, h2⟩ := (h (r₁ := E) (r₂ := A) (r₃ := B) (fun h _ => h.elim))
    (show (E ⊔ A) 0 1 from Or.inr (by simp [A])) (show B 0 2 by simp [B])
  simp [B] at h1

-- `Relation.Commute.join_left` idx 4: necessary (r₁ = 0→1, r₂ empty, r₃ = 0→2)
theorem c40 : ¬ drop0% Relation.Commute.join_left 4 := fun h => ABnc fun h1 h2 => by
  obtain ⟨d, e1, e2⟩ := (h (r₁ := A) (r₂ := E) (r₃ := B) (commEr B)) (rtgMono (fun _ _ h => Or.inl h) h1) h2
  exact ⟨d, e1, rtgSupE e2⟩

-- `Relation.Commute.join_left` idx 5: necessary (r₁ empty, r₂ = 0→1, r₃ = 0→2)
theorem c41 : ¬ drop0% Relation.Commute.join_left 5 := fun h => ABnc fun h1 h2 => by
  obtain ⟨d, e1, e2⟩ := (h (r₁ := E) (r₂ := A) (r₃ := B) (commEr B)) (rtgMono (fun _ _ h => Or.inr h) h1) h2
  exact ⟨d, e1, rtgESup e2⟩

-- `Relation.Commute.join_confluent` idx 3: necessary (r₁ = 0→1, 0→2; r₂ empty)
theorem c42 : ¬ drop0% Relation.Commute.join_confluent 3 := fun h => R5nc fun h1 h2 => by
  obtain ⟨d, e1, e2⟩ := (h (r₁ := R5) (r₂ := E) confE (commrE R5))
    (rtgMono (fun _ _ h => Or.inl h) h1) (rtgMono (fun _ _ h => Or.inl h) h2)
  exact ⟨d, rtgSupE e1, rtgSupE e2⟩

-- `Relation.Commute.join_confluent` idx 4: necessary (r₁ empty; r₂ = 0→1, 0→2)
theorem c43 : ¬ drop0% Relation.Commute.join_confluent 4 := fun h => R5nc fun h1 h2 => by
  obtain ⟨d, e1, e2⟩ := (h (r₁ := E) (r₂ := R5) confE (commEr R5))
    (rtgMono (fun _ _ h => Or.inr h) h1) (rtgMono (fun _ _ h => Or.inr h) h2)
  exact ⟨d, rtgESup e1, rtgESup e2⟩

-- `Relation.Commute.join_confluent` idx 5: necessary (r₁ = 0→1, r₂ = 0→2, both confluent)
theorem c44 : ¬ drop0% Relation.Commute.join_confluent 5 := fun h => by
  obtain ⟨d, h1, h2⟩ := (h (r₁ := A) (r₂ := B) confA confB)
    (show ReflTransGen (A ⊔ B) 0 1 from .single (Or.inl (by simp [A])))
    (show ReflTransGen (A ⊔ B) 0 2 from .single (Or.inr (by simp [B])))
  have a := rtgInv (fun c => c = 1) (by intro a b hab ha; rcases hab with hab | hab <;> simp [A, B] at hab <;> omega) h1 rfl
  have b := rtgInv (fun c => c = 2) (by intro a b hab ha; rcases hab with hab | hab <;> simp [A, B] at hab <;> omega) h2 rfl
  omega

-- `Relation.RightUnique.to_confluent` idx 2: necessary (0→1, 0→2)
theorem c45 : ¬ drop0% Relation.RightUnique.to_confluent 2 := fun h => R5nc (h (r := R5))

-- `Relation.RightUnique.toConfluent` idx 2: necessary (0→1, 0→2)
theorem c46 : ¬ drop0% Relation.RightUnique.toConfluent 2 := fun h => R5nc (h (r := R5))


-- `Relation.dom_mono` idx 4: necessary (full vs empty relation on Unit)
theorem d47 : ¬ drop0% Relation.dom_mono 4 := fun h => by
  have := @h Unit Unit (fun _ _ => True) (fun _ _ => False) () ⟨(), trivial⟩
  simp [Relation.dom] at this

-- `Relation.cod_mono` idx 4: necessary (full vs empty relation on Unit)
theorem d48 : ¬ drop0% Relation.cod_mono 4 := fun h => by
  have := @h Unit Unit (fun _ _ => True) (fun _ _ => False) () ⟨(), trivial⟩
  simp [Relation.cod] at this

-- `Std.Trichotomous.subsingleton_cod` idx 2: necessary (empty relation on Bool)
theorem d49 : ¬ drop0% Std.Trichotomous.subsingleton_cod 2 := fun h => by
  have := (@h Bool (fun _ _ => False)).elim ⟨true, fun ⟨_, h⟩ => h⟩ ⟨false, fun ⟨_, h⟩ => h⟩
  exact absurd (congrArg Subtype.val this) (by decide)

-- `Std.Trichotomous.subsingleton_dom` idx 2: necessary (empty relation on Bool)
theorem d50 : ¬ drop0% Std.Trichotomous.subsingleton_dom 2 := fun h => by
  have := (@h Bool (fun _ _ => False)).elim ⟨true, fun ⟨_, h⟩ => h⟩ ⟨false, fun ⟨_, h⟩ => h⟩
  exact absurd (congrArg Subtype.val this) (by decide)

-- `Relation.refl_serial` idx 2: necessary (empty relation on Unit)
theorem d51 : ¬ drop0% Relation.refl_serial 2 := fun h => by
  obtain ⟨b, hb⟩ := (@h Unit (fun _ _ => False)).serial ()
  exact hb

-- `Relation.instSerialOfRefl` idx 2: necessary (empty relation on Unit)
theorem d52 : ¬ drop0% Relation.instSerialOfRefl 2 := fun h => by
  obtain ⟨b, hb⟩ := (@h Unit (fun _ _ => False)).serial ()
  exact hb

-- `Relation.RightEuclidean.trichotomous_trans` idx 3: necessary (0 → 1 plus clique {1, 2})
theorem d53 : ¬ drop0% Relation.RightEuclidean.trichotomous_trans 3 := fun h => reNT (@h ℕ RE _)

-- `Relation.RightEuclidean.antisymm_rightUnique` idx 2: necessary (0 → 1, 0 → 2)
theorem d54 : ¬ drop0% Relation.RightEuclidean.antisymm_rightUnique 2 := fun h => by
  have := @h ℕ (fun a b => a = 0 ∧ (b = 1 ∨ b = 2)) ⟨fun a b h1 h2 => by omega⟩ 0 1 2 (by simp) (by simp)
  omega

-- `Relation.RightEuclidean.antisymm_rightUnique` idx 3: necessary (full relation on Bool)
theorem d55 : ¬ drop0% Relation.RightEuclidean.antisymm_rightUnique 3 := fun h => by
  have := @h Bool (fun _ _ => True) ⟨fun _ _ => trivial⟩ true true false trivial trivial
  simp at this

-- `Relation.RightEuclidean.rightUnique_antisymm` idx 2: necessary (negation on Bool)
theorem d56 : ¬ drop0% Relation.RightEuclidean.rightUnique_antisymm 2 := fun h => by
  have := (@h Bool Ng ngRU).antisymm true false (by simp [Ng]) (by simp [Ng])
  simp at this

-- `Relation.RightEuclidean.rightUnique_trans` idx 2: necessary (negation on Bool)
theorem d57 : ¬ drop0% Relation.RightEuclidean.rightUnique_trans 2 := fun h => ngNT (@h Bool Ng ngRU)

-- `Relation.RightEuclidean.rightUnique_trans` idx 3: necessary (0 → 1 plus clique {1, 2})
theorem d58 : ¬ drop0% Relation.RightEuclidean.rightUnique_trans 3 := fun h => reNT (@h ℕ RE _)

-- `Relation.RightEuclidean.rightTotal_equiv` idx 2: necessary (negation on Bool)
theorem d59 : ¬ drop0% Relation.RightEuclidean.rightTotal_equiv 2 := fun h => by
  have := (@h Bool Ng ngRT).refl true
  simp [Ng] at this

-- `Relation.RightEuclidean.leftTotal_rightUnique_trans` idx 2: necessary (single edge 0 → 1)
theorem d60 : ¬ drop0% Relation.RightEuclidean.leftTotal_rightUnique_trans 2 := fun h =>
  aNRE (@h ℕ A (fun _ _ _ h1 h2 => by simp only [A] at *; omega) aT)

-- `Relation.RightEuclidean.leftTotal_rightUnique_trans` idx 3: necessary (≤ on ℕ)
theorem d61 : ¬ drop0% Relation.RightEuclidean.leftTotal_rightUnique_trans 3 := fun h => by
  have := (@h ℕ (· ≤ ·) (fun a => ⟨a, le_rfl⟩) inferInstance).rightEuclidean (a := 0) (b := 2) (c := 1)
    (by omega) (by omega)
  omega

-- `Relation.RightEuclidean.leftTotal_rightUnique_trans` idx 4: necessary (negation on Bool)
theorem d62 : ¬ drop0% Relation.RightEuclidean.leftTotal_rightUnique_trans 4 := fun h => by
  have := (@h Bool Ng ngLT ngRU).rightEuclidean (a := true) (b := false) (c := false) (by simp [Ng]) (by simp [Ng])
  simp [Ng] at this

-- `_private.Cslib.Foundations.Relation.Euclidean.0.Relation.RightEuclidean.three_contra` idx 2: necessary (< on ℕ)
theorem d63 : ¬ drop0% _private.Cslib.Foundations.Relation.Euclidean.«0».Relation.RightEuclidean.three_contra 2 :=
  fun h => @h ℕ (· < ·) ⟨fun a b h1 h2 => by omega⟩ ⟨fun a b h1 h2 => by omega⟩ ⟨0, 1, 2, by omega⟩

-- `_private.Cslib.Foundations.Relation.Euclidean.0.Relation.RightEuclidean.three_contra` idx 3: necessary (empty relation on ℕ)
theorem d64 : ¬ drop0% _private.Cslib.Foundations.Relation.Euclidean.«0».Relation.RightEuclidean.three_contra 3 :=
  fun h => @h ℕ (fun _ _ => False) ⟨fun h _ => h⟩ ⟨fun a b h1 h2 => h1.elim⟩ ⟨0, 1, 2, by omega⟩

-- `_private.Cslib.Foundations.Relation.Euclidean.0.Relation.RightEuclidean.three_contra` idx 4: necessary (full relation on ℕ)
theorem d65 : ¬ drop0% _private.Cslib.Foundations.Relation.Euclidean.«0».Relation.RightEuclidean.three_contra 4 :=
  fun h => @h ℕ (fun _ _ => True) ⟨fun _ _ => trivial⟩ ⟨fun a b h1 h2 => (h1 trivial).elim⟩ ⟨0, 1, 2, by omega⟩

-- `Relation.RightEuclidean.trichotomous_antisymm_finite` idx 2: necessary (< on ℕ)
theorem d66 : ¬ drop0% Relation.RightEuclidean.trichotomous_antisymm_finite 2 :=
  fun h => @not_finite ℕ _ (@h ℕ (· < ·) ⟨fun a b h1 h2 => by omega⟩ ⟨fun a b h1 h2 => by omega⟩)

-- `Relation.RightEuclidean.trichotomous_antisymm_finite` idx 3: necessary (empty relation on ℕ)
theorem d67 : ¬ drop0% Relation.RightEuclidean.trichotomous_antisymm_finite 3 :=
  fun h => @not_finite ℕ _ (@h ℕ (fun _ _ => False) ⟨fun h _ => h⟩ ⟨fun a b h1 h2 => h1.elim⟩)

-- `Relation.RightEuclidean.trichotomous_antisymm_finite` idx 4: necessary (full relation on ℕ)
theorem d68 : ¬ drop0% Relation.RightEuclidean.trichotomous_antisymm_finite 4 :=
  fun h => @not_finite ℕ _ (@h ℕ (fun _ _ => True) ⟨fun _ _ => trivial⟩ ⟨fun a b h1 h2 => (h1 trivial).elim⟩)

-- `Relation.RightEuclidean.trichotomous_antisymm_card` idx 2: necessary (< on Fin 3)
theorem d69 : ¬ drop0% Relation.RightEuclidean.trichotomous_antisymm_card 2 := fun h => by
  have := @h (Fin 3) (· < ·) ⟨fun a b h1 h2 => le_antisymm (not_lt.mp h2) (not_lt.mp h1)⟩
    ⟨fun a b h1 h2 => absurd h1 (lt_asymm h2)⟩ inferInstance
  simp at this

-- `Relation.RightEuclidean.trichotomous_antisymm_card` idx 3: necessary (empty relation on Fin 3)
theorem d70 : ¬ drop0% Relation.RightEuclidean.trichotomous_antisymm_card 3 := fun h => by
  have := @h (Fin 3) (fun _ _ => False) ⟨fun h _ => h⟩ ⟨fun a b h1 h2 => h1.elim⟩ inferInstance
  simp at this

-- `Relation.RightEuclidean.trichotomous_antisymm_card` idx 4: necessary (full relation on Fin 3)
theorem d71 : ¬ drop0% Relation.RightEuclidean.trichotomous_antisymm_card 4 := fun h => by
  have := @h (Fin 3) (fun _ _ => True) ⟨fun _ _ => trivial⟩ ⟨fun a b h1 h2 => (h1 trivial).elim⟩ inferInstance
  simp at this

-- `Relation.RightEuclidean.cod_subset_dom` idx 2: necessary (single edge 0 → 1)
theorem d72 : ¬ drop0% Relation.RightEuclidean.cod_subset_dom 2 := fun h => by
  obtain ⟨b, hb⟩ := @h ℕ A 1 ⟨0, by simp [A]⟩
  simp [A] at hb

-- `Relation.RightEuclidean.equiv_cod` idx 2: necessary (single edge 0 → 1)
theorem d73 : ¬ drop0% Relation.RightEuclidean.equiv_cod 2 := fun h => by
  have := (@h ℕ A).refl ⟨1, 0, by simp [A]⟩
  simp [A] at this

-- `Relation.LeftEuclidean.reflOn_dom` idx 2: necessary (single edge 0 → 1)
theorem d74 : ¬ drop0% Relation.LeftEuclidean.reflOn_dom 2 := fun h => by
  have := @h ℕ A 0 ⟨1, by simp [A]⟩
  simp [A] at this

-- `Relation.LeftEuclidean.trichotomous_trans` idx 3: necessary (converse of 0 → 1 plus clique {1, 2})
theorem d75 : ¬ drop0% Relation.LeftEuclidean.trichotomous_trans 3 := fun h => leNT (@h ℕ LE' _)

-- `Relation.LeftEuclidean.antisymm_leftUnique` idx 3: necessary (full relation on Bool)
theorem d76 : ¬ drop0% Relation.LeftEuclidean.antisymm_leftUnique 3 := fun h => by
  have := @h Bool (fun _ _ => True) ⟨fun _ _ => trivial⟩ true false true trivial trivial
  simp at this

-- `Relation.LeftEuclidean.leftUnique_antisymm` idx 2: necessary (negation on Bool)
theorem d77 : ¬ drop0% Relation.LeftEuclidean.leftUnique_antisymm 2 := fun h => by
  have := (@h Bool Ng ngLU).antisymm true false (by simp [Ng]) (by simp [Ng])
  simp at this

-- `Relation.LeftEuclidean.leftUnique_trans` idx 2: necessary (negation on Bool)
theorem d78 : ¬ drop0% Relation.LeftEuclidean.leftUnique_trans 2 := fun h => ngNT (@h Bool Ng ngLU)

-- `Relation.LeftEuclidean.leftUnique_trans` idx 3: necessary (converse of 0 → 1 plus clique {1, 2})
theorem d79 : ¬ drop0% Relation.LeftEuclidean.leftUnique_trans 3 := fun h => leNT (@h ℕ LE' _)

-- `Relation.LeftEuclidean.leftTotal_equiv` idx 2: necessary (negation on Bool)
theorem d80 : ¬ drop0% Relation.LeftEuclidean.leftTotal_equiv 2 := fun h => by
  have := (@h Bool Ng ngLT).refl true
  simp [Ng] at this

-- `Relation.LeftEuclidean.rightTotal_leftUnique_trans` idx 2: necessary (single edge 0 → 1)
theorem d81 : ¬ drop0% Relation.LeftEuclidean.rightTotal_leftUnique_trans 2 := fun h =>
  aNLE (@h ℕ A (fun _ _ _ h1 h2 => by simp only [A] at *; omega) aT)

-- `Relation.LeftEuclidean.rightTotal_leftUnique_trans` idx 3: necessary (≤ on ℕ)
theorem d82 : ¬ drop0% Relation.LeftEuclidean.rightTotal_leftUnique_trans 3 := fun h => by
  have := (@h ℕ (· ≤ ·) (fun a => ⟨a, le_rfl⟩) inferInstance).leftEuclidean (a := 1) (b := 0) (c := 2)
    (by omega) (by omega)
  omega

-- `Relation.LeftEuclidean.rightTotal_leftUnique_trans` idx 4: necessary (negation on Bool)
theorem d83 : ¬ drop0% Relation.LeftEuclidean.rightTotal_leftUnique_trans 4 := fun h => by
  have := (@h Bool Ng ngRT ngLU).leftEuclidean (a := true) (b := true) (c := false) (by simp [Ng]) (by simp [Ng])
  simp [Ng] at this

-- `Relation.LeftEuclidean.trichotomous_antisymm_finite` idx 2: necessary (< on ℕ)
theorem d84 : ¬ drop0% Relation.LeftEuclidean.trichotomous_antisymm_finite 2 :=
  fun h => @not_finite ℕ _ (@h ℕ (· < ·) ⟨fun a b h1 h2 => by omega⟩ ⟨fun a b h1 h2 => by omega⟩)

-- `Relation.LeftEuclidean.trichotomous_antisymm_finite` idx 3: necessary (empty relation on ℕ)
theorem d85 : ¬ drop0% Relation.LeftEuclidean.trichotomous_antisymm_finite 3 :=
  fun h => @not_finite ℕ _ (@h ℕ (fun _ _ => False) ⟨fun h _ => h⟩ ⟨fun a b h1 h2 => h1.elim⟩)

-- `Relation.LeftEuclidean.trichotomous_antisymm_finite` idx 4: necessary (full relation on ℕ)
theorem d86 : ¬ drop0% Relation.LeftEuclidean.trichotomous_antisymm_finite 4 :=
  fun h => @not_finite ℕ _ (@h ℕ (fun _ _ => True) ⟨fun _ _ => trivial⟩ ⟨fun a b h1 h2 => (h1 trivial).elim⟩)

-- `Relation.LeftEuclidean.trichotomous_antisymm_card` idx 2: necessary (< on Fin 3)
theorem d87 : ¬ drop0% Relation.LeftEuclidean.trichotomous_antisymm_card 2 := fun h => by
  have := @h (Fin 3) (· < ·) ⟨fun a b h1 h2 => le_antisymm (not_lt.mp h2) (not_lt.mp h1)⟩
    ⟨fun a b h1 h2 => absurd h1 (lt_asymm h2)⟩ inferInstance
  simp at this

-- `Relation.LeftEuclidean.trichotomous_antisymm_card` idx 3: necessary (empty relation on Fin 3)
theorem d88 : ¬ drop0% Relation.LeftEuclidean.trichotomous_antisymm_card 3 := fun h => by
  have := @h (Fin 3) (fun _ _ => False) ⟨fun h _ => h⟩ ⟨fun a b h1 h2 => h1.elim⟩ inferInstance
  simp at this

-- `Relation.LeftEuclidean.trichotomous_antisymm_card` idx 4: necessary (full relation on Fin 3)
theorem d89 : ¬ drop0% Relation.LeftEuclidean.trichotomous_antisymm_card 4 := fun h => by
  have := @h (Fin 3) (fun _ _ => True) ⟨fun _ _ => trivial⟩ ⟨fun a b h1 h2 => (h1 trivial).elim⟩ inferInstance
  simp at this

-- `Relation.LeftEuclidean.dom_subset_cod` idx 2: necessary (single edge 0 → 1)
theorem d90 : ¬ drop0% Relation.LeftEuclidean.dom_subset_cod 2 := fun h => by
  obtain ⟨b, hb⟩ := @h ℕ A 0 ⟨1, by simp [A]⟩
  simp [A] at hb

-- `Relation.LeftEuclidean.leftTotal_dom` idx 2: necessary (single edge 0 → 1)
theorem d91 : ¬ drop0% Relation.LeftEuclidean.leftTotal_dom 2 := fun h => by
  obtain ⟨⟨b, c, hc⟩, hb⟩ := @h ℕ A ⟨0, 1, by simp [A]⟩
  simp [A] at hb hc; omega

-- `Relation.LeftEuclidean.equiv_dom` idx 2: necessary (single edge 0 → 1)
theorem d92 : ¬ drop0% Relation.LeftEuclidean.equiv_dom 2 := fun h => by
  have := (@h ℕ A).refl ⟨0, 1, by simp [A]⟩
  simp [A] at this

-- `_private.Cslib.Foundations.Relation.Euclidean.0.Relation.symm_equivalents` idx 2: necessary (single edge 0 → 1)
theorem d93 : ¬ drop0% _private.Cslib.Foundations.Relation.Euclidean.«0».Relation.symm_equivalents 2 :=
  fun h => aNRE (((@h ℕ A).out 3 1).mp aT)

-- `Relation.symm_leftEuclidean_iff_rightEuclidean` idx 2: necessary (0 → 1 plus clique {1, 2})
theorem d94 : ¬ drop0% Relation.symm_leftEuclidean_iff_rightEuclidean 2 :=
  fun h => reNLE ((@h ℕ RE).mpr reRE)

-- `Relation.symm_leftEuclidean_iff_trans` idx 2: necessary (single edge 0 → 1)
theorem d95 : ¬ drop0% Relation.symm_leftEuclidean_iff_trans 2 := fun h => aNLE ((@h ℕ A).mpr aT)

-- `Relation.symm_rightEuclidean_iff_trans` idx 2: necessary (single edge 0 → 1)
theorem d96 : ¬ drop0% Relation.symm_rightEuclidean_iff_trans 2 := fun h => aNRE ((@h ℕ A).mpr aT)

-- `Relation.leftEuclidean_rightEuclidean_dom_cod_eq` idx 2: necessary (0 → 1 plus clique {1, 2}; 0 ∉ cod)
theorem d97 : ¬ drop0% Relation.leftEuclidean_rightEuclidean_dom_cod_eq 2 := fun h => by
  have h0 : (0 : ℕ) ∈ Relation.dom RE := ⟨1, by simp [RE]⟩
  rw [@h ℕ RE reRE] at h0
  obtain ⟨a, ha⟩ := h0
  simp [RE] at ha

-- `Relation.leftEuclidean_rightEuclidean_dom_cod_eq` idx 3: necessary (converse; 0 ∉ dom)
theorem d98 : ¬ drop0% Relation.leftEuclidean_rightEuclidean_dom_cod_eq 3 := fun h => by
  have h0 : (0 : ℕ) ∈ Relation.cod LE' := ⟨1, by simp [LE', RE]⟩
  rw [← @h ℕ LE' leLE] at h0
  obtain ⟨a, ha⟩ := h0
  simp [LE', RE] at ha

-- `Relation.dom_cod_leftEuclidean` idx 2: necessary (0 → 0, 1 → 1, 0 → 2, 1 → 2: equivalence on dom, 2 ∉ dom)
theorem d99 : ¬ drop0% Relation.dom_cod_leftEuclidean 2 := fun h => by
  have := (@h ℕ RD rdEq).leftEuclidean (a := 0) (b := 1) (c := 2) (by simp [RD]) (by simp [RD])
  simp [RD] at this

-- `Relation.RelatesInSteps.head_induction_on` idx 6: necessary (dependent; empty relation, a = 1, b = 0, n = 0)
theorem d100 : ¬ indep0% Relation.RelatesInSteps.head_induction_on 6 := fun h => by
  have := risE (@h ℕ E 0 (fun _ _ _ => True) 1 0 trivial (fun _ _ _ => trivial))
  omega

-- `Relation.RelatesInSteps.head_induction_on` idx 7: necessary (motive constantly False, h = refl)
theorem d101 : ¬ drop0% Relation.RelatesInSteps.head_induction_on 7 := fun h =>
  @h ℕ E 0 (fun _ _ _ => False) 0 0 (.refl 0) (fun _ _ ih => ih)

-- `Relation.RelatesInSteps.head_induction_on` idx 8: necessary (motive n = 0, one step 0 → 1)
theorem d102 : ¬ drop0% Relation.RelatesInSteps.head_induction_on 8 := fun h => by
  have := @h ℕ A 1 (fun _ n _ => n = 0) 0 1 (.single (by simp [A])) rfl
  simp at this

-- `Relation.RelatesInSteps.exists_isChainFromTo` idx 5: necessary (empty relation, n = 1)
theorem d103 : ¬ drop0% Relation.RelatesInSteps.exists_isChainFromTo 5 := fun h => by
  obtain ⟨l, hl, hlen⟩ := @h ℕ E 0 0 1
  match l, hl, hlen with
  | [x, y], hl, _ => exact (List.isChain_pair.mp hl.isChain)

-- `List.IsChain.relatesInSteps_getElem` idx 3: necessary (empty relation, chain [0, 0])
theorem d104 : ¬ drop0% List.IsChain.relatesInSteps_getElem 3 := fun h => by
  have := @h ℕ E [0, 0] 0 1 (by simp)
  cases this with
  | tail _ _ _ _ h2 => exact h2

-- `Relation.RelatesWithinSteps.map` idx 5: necessary (r = 0 → 1, r' empty, g = id)
theorem d105 : ¬ drop0% Relation.RelatesWithinSteps.map 5 := fun h => by
  obtain ⟨m, _, hm⟩ := @h ℕ ℕ A E id 0 1 1 ⟨1, le_rfl, .single (by simp [A])⟩
  have := risE hm
  simp at this

-- `Set.ReflOn.of_dom` idx 5: necessary (empty relation)
theorem d106 : ¬ drop0% Set.ReflOn.of_dom 5 := fun h =>
  @h ℕ 0 0 E (fun _ ⟨_, h⟩ => h.elim)

-- `Set.ReflOn.of_cod` idx 5: necessary (empty relation)
theorem d107 : ¬ drop0% Set.ReflOn.of_cod 5 := fun h =>
  @h ℕ 0 0 E (fun _ ⟨_, h⟩ => h.elim)

-- `Set.SymmOn.of_dom` idx 6: necessary (single edge 0 → 1, a = 5, b = 0, c = 1)
theorem d108 : ¬ drop0% Set.SymmOn.of_dom 6 := fun h => by
  have := @h ℕ 5 0 1 A (fun a ⟨_, ha⟩ b ⟨_, hb⟩ hab => by simp only [A] at *; omega) (by simp [A])
  simp [A] at this

-- `Set.SymmOn.of_cod` idx 6: necessary (single edge 0 → 1, a = 1, b = 5, c = 0)
theorem d109 : ¬ drop0% Set.SymmOn.of_cod 6 := fun h => by
  have := @h ℕ 1 5 0 A (fun a ⟨_, ha⟩ b ⟨_, hb⟩ hab => by simp only [A] at *; omega) (by simp [A])
  simp [A] at this

-- `Set.SymmOn.of_cod` idx 7: necessary (single edge 0 → 1, a = 0, b = 1)
theorem d110 : ¬ drop0% Set.SymmOn.of_cod 7 := fun h => by
  have := @h ℕ 0 1 0 A (fun a ⟨_, ha⟩ b ⟨_, hb⟩ hab => by simp only [A] at *; omega) (by simp [A])
  simp [A] at this

-- `Relation.SN.intro` idx 3: necessary (full relation on Unit)
theorem d111 : ¬ drop0% Relation.SN.intro 3 := fun h => notSNU (@h Unit U ())

-- `Relation.SN.transGen` idx 3: necessary (full relation on Unit)
theorem d112 : ¬ drop0% Relation.SN.transGen 3 := fun h =>
  notSNU ((SN.iff_transGen ()).mp (@h Unit U ()))

-- `Relation.SN.of_le` idx 4: necessary (full relation on Unit)
theorem d113 : ¬ drop0% Relation.SN.of_le 4 := fun h => notSNU (@h Unit U () U le_rfl)

-- `Relation.SN.of_le` idx 5: necessary (r empty, r' full on Unit)
theorem d114 : ¬ drop0% Relation.SN.of_le 5 := fun h =>
  notSNU (@h Unit (fun _ _ => False) () U (SN.of_normal (fun ⟨_, h⟩ => h)))

-- `Relation.SN.of_normal` idx 3: necessary (full relation on Unit)
theorem d115 : ¬ drop0% Relation.SN.of_normal 3 := fun h => notSNU (@h Unit U ())

-- `Relation.Terminating.to_transGen` idx 2: necessary (full relation on Unit)
theorem d116 : ¬ drop0% Relation.Terminating.to_transGen 2 := fun h =>
  notTermU (Terminating.of_transGen (@h Unit U))

-- `Relation.Terminating.toTransGen` idx 2: necessary (full relation on Unit)
theorem d117 : ¬ drop0% Relation.Terminating.toTransGen 2 := fun h =>
  notTermU (Terminating.of_transGen (@h Unit U))

-- `Relation.Terminating.to_acyclic` idx 2: necessary (full relation on Unit)
theorem d118 : ¬ drop0% Relation.Terminating.to_acyclic 2 := fun h =>
  (@h Unit U).irrefl () (.single trivial)

-- `Relation.Terminating.toAcyclic` idx 2: necessary (full relation on Unit)
theorem d119 : ¬ drop0% Relation.Terminating.toAcyclic 2 := fun h =>
  (@h Unit U).irrefl () (.single trivial)

-- `Relation.Terminating.of_transGen` idx 2: necessary (full relation on Unit)
theorem d120 : ¬ drop0% Relation.Terminating.of_transGen 2 := fun h => notTermU (@h Unit U)

-- `Relation.Terminating.ofTransGen` idx 2: necessary (full relation on Unit)
theorem d121 : ¬ drop0% Relation.Terminating.ofTransGen 2 := fun h => notTermU (@h Unit U)

-- `Relation.Terminating.of_le` idx 3: necessary (full relation on Unit)
theorem d122 : ¬ drop0% Relation.Terminating.of_le 3 := fun h => notTermU (@h Unit U U le_rfl)

-- `Relation.Terminating.of_le` idx 4: necessary (r empty, r' full on Unit)
theorem d123 : ¬ drop0% Relation.Terminating.of_le 4 := fun h =>
  notTermU (@h Unit (fun _ _ => False) U (Terminating.iff_forall_sn.mpr fun _ => SN.of_normal (fun ⟨_, h⟩ => h)))
