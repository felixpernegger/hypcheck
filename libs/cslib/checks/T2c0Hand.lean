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

namespace T2c0
open Pointwise Cslib

/-- Subsets of ℤ that are periodic away from 0. -/
def PerP (S : Set ℤ) : Prop :=
  ∃ n : ℤ, n ≠ 0 ∧ ∀ x y : ℤ, x ≠ 0 → y ≠ 0 → n ∣ x - y → (x ∈ S ↔ y ∈ S)

theorem per_union {S T : Set ℤ} (hS : PerP S) (hT : PerP T) : PerP (S ∪ T) := by
  obtain ⟨n, hn, hS⟩ := hS
  obtain ⟨m, hm, hT⟩ := hT
  refine ⟨n * m, mul_ne_zero hn hm, fun x y hx hy hd => ?_⟩
  simp only [Set.mem_union, hS x y hx hy (dvd_trans (dvd_mul_right n m) hd),
    hT x y hx hy (dvd_trans (dvd_mul_left m n) hd)]

theorem per_inter {S T : Set ℤ} (hS : PerP S) (hT : PerP T) : PerP (S ∩ T) := by
  obtain ⟨n, hn, hS⟩ := hS
  obtain ⟨m, hm, hT⟩ := hT
  refine ⟨n * m, mul_ne_zero hn hm, fun x y hx hy hd => ?_⟩
  simp only [Set.mem_inter_iff, hS x y hx hy (dvd_trans (dvd_mul_right n m) hd),
    hT x y hx hy (dvd_trans (dvd_mul_left m n) hd)]

theorem per_compl {S : Set ℤ} (hS : PerP S) : PerP Sᶜ := by
  obtain ⟨n, hn, hS⟩ := hS
  exact ⟨n, hn, fun x y hx hy hd => not_congr (hS x y hx hy hd)⟩

theorem per_neg {S : Set ℤ} (hS : PerP S) : PerP (-S) := by
  obtain ⟨n, hn, hS⟩ := hS
  refine ⟨n, hn, fun x y hx hy hd => ?_⟩
  obtain ⟨k, hk⟩ := hd
  simp only [Set.mem_neg]
  exact hS (-x) (-y) (neg_ne_zero.2 hx) (neg_ne_zero.2 hy) ⟨-k, by linear_combination -hk⟩

theorem per_zero : PerP (0 : Set ℤ) :=
  ⟨1, one_ne_zero, fun x y hx hy _ => by simp [Set.mem_zero, hx, hy]⟩

theorem per_bot : PerP (⊥ : Set ℤ) := ⟨1, one_ne_zero, fun x y _ _ _ => by simp⟩

theorem per_add {S T : Set ℤ} (hS : PerP S) (hT : PerP T) : PerP (S + T) := by
  obtain ⟨n, hn, hS⟩ := hS
  obtain ⟨m, hm, hT⟩ := hT
  have key : ∀ x y, x ≠ 0 → y ≠ 0 → n * m ∣ x - y → x ∈ S + T → y ∈ S + T := by
    intro x y hx hy hd hxm
    obtain ⟨s, hs, t, ht, rfl⟩ := Set.mem_add.1 hxm
    obtain ⟨c, hc⟩ := hd
    have mS : ∀ s', s ≠ 0 → s' ≠ 0 → n ∣ s - s' → s' ∈ S :=
      fun s' h1 h2 h3 => (hS s s' h1 h2 h3).1 hs
    have mT : ∀ t', t ≠ 0 → t' ≠ 0 → m ∣ t - t' → t' ∈ T :=
      fun t' h1 h2 h3 => (hT t t' h1 h2 h3).1 ht
    rw [Set.mem_add]
    by_cases hA : s ≠ 0 ∧ y - t ≠ 0
    · exact ⟨y - t, mS _ hA.1 hA.2 ⟨m * c, by linear_combination hc⟩, t, ht, by ring⟩
    by_cases hB : t ≠ 0 ∧ y - s ≠ 0
    · exact ⟨s, hs, y - t + t - s, mT _ hB.1 (by rw [sub_add_cancel]; exact hB.2)
        ⟨n * c, by linear_combination hc⟩, by ring⟩
    have hs0 : s ≠ 0 := by rintro rfl; simp_all
    have hyt : y = t := by by_contra h; exact hA ⟨hs0, sub_ne_zero.2 h⟩
    have hys : y = s := by
      by_contra h; refine hB ⟨?_, sub_ne_zero.2 h⟩; rintro rfl; exact hy hyt
    subst hyt
    have hsc : s = n * m * c := by linear_combination hc
    by_cases hk : s + n * m = 0
    · refine ⟨s - n * m, mS _ hs0 (by rw [← hys]; intro h; apply mul_ne_zero hn hm; linarith)
        ⟨m, by ring⟩, n * m, mT _ hy (mul_ne_zero hn hm)
        ⟨n * (c - 1), by linear_combination hsc + hys⟩, by linarith⟩
    · refine ⟨s + n * m, mS _ hs0 hk ⟨-m, by ring⟩, -(n * m), mT _ hy
        (neg_ne_zero.2 (mul_ne_zero hn hm)) ⟨n * (c + 1), by linear_combination hsc + hys⟩,
        by linarith⟩
  refine ⟨n * m, mul_ne_zero hn hm, fun x y hx hy hd =>
    ⟨key x y hx hy hd, key y x hy hx ((dvd_sub_comm).1 hd)⟩⟩

/-- The Boolean algebra of subsets of ℤ periodic away from 0. -/
def PZ := {S : Set ℤ // PerP S}

instance : Max PZ := ⟨fun a b => ⟨a.1 ∪ b.1, per_union a.2 b.2⟩⟩
instance : Min PZ := ⟨fun a b => ⟨a.1 ∩ b.1, per_inter a.2 b.2⟩⟩
instance : Bot PZ := ⟨⟨⊥, per_bot⟩⟩
instance : Top PZ := ⟨⟨⊤, by simpa using per_compl per_bot⟩⟩
instance : Compl PZ := ⟨fun a => ⟨a.1ᶜ, per_compl a.2⟩⟩
instance : SDiff PZ := ⟨fun a b => ⟨a.1 \ b.1, by rw [Set.sdiff_eq]; exact per_inter a.2 (per_compl b.2)⟩⟩
instance : HImp PZ := ⟨fun a b => ⟨a.1 ⇨ b.1, by rw [himp_eq]; exact per_union b.2 (per_compl a.2)⟩⟩
instance : LE PZ := ⟨fun a b => a.1 ≤ b.1⟩
instance : LT PZ := ⟨fun a b => a.1 < b.1⟩
theorem pzInj : Function.Injective (fun a : PZ => a.1) := fun a b h => Subtype.ext h

instance PZba : BooleanAlgebra PZ :=
  pzInj.booleanAlgebra _ Iff.rfl Iff.rfl (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem le_iff {a b : PZ} : a ≤ b ↔ a.1 ⊆ b.1 := Iff.rfl

/-- A non-atomic integral relation algebra: a subalgebra of the complex algebra of ℤ. -/
instance PZra : RelationAlgebra PZ where
  __ := PZba
  mul a b := ⟨a.1 + b.1, per_add a.2 b.2⟩
  one := ⟨0, per_zero⟩
  mul_assoc a b c := Subtype.ext (add_assoc _ _ _)
  one_mul a := Subtype.ext (zero_add _)
  mul_one a := Subtype.ext (add_zero _)
  star a := ⟨-a.1, per_neg a.2⟩
  star_involutive a := Subtype.ext (neg_neg _)
  star_mul a b := Subtype.ext (neg_add_rev _ _)
  sup_mul a b c := Subtype.ext (Set.union_add)
  star_sup a b := Subtype.ext (Set.union_neg (s := a.1) (t := b.1))
  tarski a b := by
    refine le_iff.2 fun x hx => ?_
    change x ∈ -a.1 + (a.1 + b.1)ᶜ at hx
    change x ∈ (b.1)ᶜ
    obtain ⟨u, hu, w, hw, rfl⟩ := Set.mem_add.1 hx
    intro hb
    exact hw (Set.mem_add.2 ⟨-u, hu, u + w, hb, by ring⟩)

theorem val_one : (1 : PZ).1 = {0} := rfl
theorem val_mul (a b : PZ) : (a * b).1 = a.1 + b.1 := rfl

theorem at1 : IsAtom (1 : PZ) := by
  refine ⟨fun h => ?_, fun q hq => ?_⟩
  · have : (0 : ℤ) ∈ (1 : PZ).1 := rfl
    rw [h] at this; exact this
  · apply Subtype.ext
    apply Set.eq_empty_of_forall_notMem
    intro z hz
    have hz0 : z = 0 := le_iff.1 hq.le hz
    subst hz0
    apply hq.ne
    apply Subtype.ext
    apply le_antisymm (le_iff.1 hq.le)
    intro w hw
    rw [val_one] at hw
    rw [Set.mem_singleton_iff.1 hw]; exact hz

theorem le11 : (1 : PZ) ≤ (1 : PZ)ᶜ * (1 : PZ)ᶜ := by
  refine le_iff.2 fun z hz => ?_
  rw [val_one, Set.mem_singleton_iff] at hz
  subst hz
  exact Set.mem_add.2 ⟨1, (show (1:ℤ) ∉ ({0} : Set ℤ) by simp), -1,
    (show (-1:ℤ) ∉ ({0} : Set ℤ) by simp), by norm_num⟩

theorem noAtom {s : PZ} (hs : IsAtom s) (hsb : s ≤ (1 : PZ)ᶜ) : False := by
  have hne : s.1.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]; intro h; exact hs.1 (Subtype.ext h)
  obtain ⟨x, hx⟩ := hne
  have hx0 : x ≠ 0 := fun h => le_iff.1 hsb hx (by rw [val_one, h]; rfl)
  obtain ⟨n, hn, hP⟩ := s.2
  have hQ : PerP {y | 2 * n ∣ y - x} := ⟨2 * n, mul_ne_zero two_ne_zero hn, fun y z _ _ h =>
    ⟨fun h1 => by simpa using dvd_sub h1 h, fun h1 => by simpa using dvd_add h h1⟩⟩
  let q : PZ := s ⊓ ⟨_, hQ⟩
  have hxq : x ∈ q.1 := ⟨hx, by simp⟩
  have hqs : q < s := by
    refine lt_of_le_of_ne inf_le_left fun h => ?_
    have h2 : ¬ 2 * n ∣ n := by
      rintro ⟨k, hk⟩
      have : n * 1 = n * (2 * k) := by linear_combination hk
      have := mul_left_cancel₀ hn this; omega
    by_cases hz : x + n = 0
    · have hm : x - n ∈ s.1 := (hP x (x - n) hx0 (by omega) ⟨1, by ring⟩).1 hx
      rw [← h] at hm
      exact h2 (by simpa using dvd_neg.2 hm.2)
    · have hm : x + n ∈ s.1 := (hP x (x + n) hx0 hz ⟨-1, by ring⟩).1 hx
      rw [← h] at hm
      exact h2 (by simpa using hm.2)
  have := hs.2 q hqs
  rw [this] at hxq; exact hxq

end T2c0

-- `Cslib.RelationAlgebra.exists_atom_le_mul_right` idx 2: necessary (subsets of ℤ periodic away from 0; p = 1 = {0}, a = b = 1ᶜ, no atom below 1ᶜ)
theorem ealr2 : ¬ drop0% Cslib.RelationAlgebra.exists_atom_le_mul_right 2 := fun H => by
  obtain ⟨s, hs, hsb, -⟩ := H (α := T2c0.PZ) (a := (1 : T2c0.PZ)ᶜ) (b := (1 : T2c0.PZ)ᶜ) (p := 1)
    T2c0.at1 T2c0.le11
  exact T2c0.noAtom hs hsb

-- `Cslib.RelationAlgebra.exists_atom_le_mul_left` idx 2: necessary (same model; no atom below a = 1ᶜ)
theorem eall2 : ¬ drop0% Cslib.RelationAlgebra.exists_atom_le_mul_left 2 := fun H => by
  obtain ⟨s, hs, hsa, -⟩ := H (α := T2c0.PZ) (a := (1 : T2c0.PZ)ᶜ) (b := (1 : T2c0.PZ)ᶜ) (p := 1)
    T2c0.at1 T2c0.le11
  exact T2c0.noAtom hs hsa
