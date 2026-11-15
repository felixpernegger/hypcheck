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

open Cslib LTS
namespace U1c0
universe u₁ u₂ u₃
section OS
variable {State₁ : Type u₁} {State₂ : Type u₂} {Label : Type u₃} {lts₁ : LTS State₁ Label}
  {lts₂ : LTS State₂ Label}

/-- With only the second LTS image-finite, a transition of the second state is matched. -/
theorem G [h2 : lts₂.ImageFinite] {s₁ : State₁} {s₂ : State₂} {μ : Label} {s₂' : State₂}
    (h : lts₁.BisimilarityApprox lts₂ (Ordinal.omega0 : Ordinal) s₁ s₂) (htr : lts₂.Tr s₂ μ s₂') :
    ∃ s₁', lts₁.Tr s₁ μ s₁' ∧ lts₁.BisimilarityApprox lts₂ (Ordinal.omega0 : Ordinal) s₁' s₂' := by
  classical
  have hn : ∀ n : ℕ, ∃ s, lts₁.Tr s₁ μ s ∧ lts₁.BisimilarityApprox lts₂ (n : ℕ) s s₂' := fun n => by
    have h' := BisimilarityApprox.omega_iff.mp h (n+1)
    have : lts₁.BisimilarityApprox lts₂ ((n : WithTop Ordinal) + 1) s₁ s₂ := by simpa using h'
    exact this.follow_snd htr
  choose f hf1 hf2 using hn
  have ht : ∀ n, ∃ t : lts₂.image s₂ μ, lts₁.BisimilarityApprox lts₂ (Ordinal.omega0 : Ordinal) (f n) t := fun n => by
    obtain ⟨t, ht, hr⟩ := BisimilarityApprox.isSimulation_omega h μ (f n) (hf1 n)
    exact ⟨⟨t, ht⟩, hr⟩
  choose g hg using ht
  haveI : Finite (lts₂.image s₂ μ) := h2 s₂ μ
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber g
  have hinf : (g ⁻¹' {y}).Infinite := Set.infinite_coe_iff.mp hy
  obtain ⟨n0, hn0⟩ := hinf.nonempty
  refine ⟨f n0, hf1 n0, ?_⟩
  rw [BisimilarityApprox.omega_iff]; intro N
  obtain ⟨n, hn, hnN⟩ := hinf.exists_gt N
  have e0 : g n0 = y := hn0
  have e1 : g n = y := hn
  have h0 := hg n0; rw [e0] at h0
  have h1 := hg n; rw [e1] at h1
  have a1 := BisimilarityApprox.omega_iff.mp h0 N
  have a2 := (BisimilarityApprox.omega_iff.mp h1 N).symm
  have a3 := (hf2 n).of_ge_nat (le_of_lt hnN)
  exact (a1.trans_nat a2).trans_nat a3

theorem OS [lts₂.ImageFinite] :
    IsBisimulation lts₁ lts₂ (fun x y => lts₁.BisimilarityApprox lts₂ (Ordinal.omega0 : Ordinal) x y) :=
  fun _ _ h μ => ⟨fun s₁' htr => BisimilarityApprox.isSimulation_omega h μ s₁' htr,
    fun _ htr => G h htr⟩

theorem OS' [lts₁.ImageFinite] :
    IsBisimulation lts₁ lts₂ (fun x y => lts₁.BisimilarityApprox lts₂ (Ordinal.omega0 : Ordinal) x y) :=
  fun _ _ h μ => ⟨fun _ htr => by
      obtain ⟨t, ht, hr⟩ := G (lts₁ := lts₂) (lts₂ := lts₁) h.symm htr
      exact ⟨t, ht, hr.symm⟩,
    fun s₂' htr => BisimilarityApprox.flip_isSimulation_omega h μ s₂' htr⟩
end OS
end U1c0
open U1c0

-- `Cslib.LTS.BisimilarityApprox.isBisimulation_omega` idx 5: removable (one image-finite side suffices)
theorem ibo5 : drop% Cslib.LTS.BisimilarityApprox.isBisimulation_omega 5 := @OS.{_,_,_}
-- `Cslib.LTS.BisimilarityApprox.isBisimulation_omega` idx 6: removable
theorem ibo6 : drop% Cslib.LTS.BisimilarityApprox.isBisimulation_omega 6 := @OS'.{_,_,_}

namespace U1c0
def LU : LTS Unit Unit := ⟨fun _ _ _ => True⟩
def LE0 : LTS Unit Unit := ⟨fun _ _ _ => False⟩

theorem nA1 (o : WithTop Ordinal) (ho : 1 ≤ o) : ¬ LU.BisimilarityApprox LE0 o () () := by
  intro h
  have h1 : LU.BisimilarityApprox LE0 (0+1) () () := by simpa using h.of_ge ho
  obtain ⟨t, ht, _⟩ := h1.follow_fst (μ := ()) (s₁' := ()) (show LU.Tr () () () from trivial)
  exact ht

theorem nBis : ¬ LU.Bisimilarity LE0 () () := fun h => nA1 1 le_rfl (h.approx 1)
instance : LU.ImageFinite := inferInstance
instance : LE0.ImageFinite := inferInstance

section
variable {State₁ : Type u₁} {State₂ : Type u₂} {Label : Type u₃} {lts₁ : LTS State₁ Label}
  {lts₂ : LTS State₂ Label}
theorem omegaBis (hb : IsBisimulation lts₁ lts₂ (fun x y => lts₁.BisimilarityApprox lts₂ (Ordinal.omega0 : Ordinal) x y))
    {o : WithTop Ordinal.{max u₁ u₂}} (ho : (Ordinal.omega0 : Ordinal) ≤ o) {s₁ : State₁} {s₂ : State₂} :
    lts₁.BisimilarityApprox lts₂ o s₁ s₂ ↔ lts₁.Bisimilarity lts₂ s₁ s₂ :=
  ⟨fun h => hb.le_bisimilarity _ _ (h.of_ge ho), fun h => h.approx o⟩
end
end U1c0
open U1c0

-- `Cslib.LTS.BisimilarityApprox.bisimilarity_of_omega` idx 7: removable
theorem bo7 : drop% Cslib.LTS.BisimilarityApprox.bisimilarity_of_omega 7 := by
  intro _ _ _ lts₁ lts₂ s₁ s₂ _ h
  exact OS.le_bisimilarity _ _ h
-- `Cslib.LTS.BisimilarityApprox.bisimilarity_of_omega` idx 8: removable
theorem bo8 : drop% Cslib.LTS.BisimilarityApprox.bisimilarity_of_omega 8 := by
  intro _ _ _ lts₁ lts₂ s₁ s₂ _ h
  exact OS'.le_bisimilarity _ _ h
-- `Cslib.LTS.BisimilarityApprox.omega_iff_bisimilarity` idx 7: removable
theorem oi7 : drop% Cslib.LTS.BisimilarityApprox.omega_iff_bisimilarity 7 := by
  intro _ _ _ lts₁ lts₂ s₁ s₂ _
  exact omegaBis OS le_rfl
-- `Cslib.LTS.BisimilarityApprox.omega_iff_bisimilarity` idx 8: removable
theorem oi8 : drop% Cslib.LTS.BisimilarityApprox.omega_iff_bisimilarity 8 := by
  intro _ _ _ lts₁ lts₂ s₁ s₂ _
  exact omegaBis OS' le_rfl
-- `Cslib.LTS.BisimilarityApprox.omega_eq_bisimilarity` idx 5: removable
theorem oe5 : drop% Cslib.LTS.BisimilarityApprox.omega_eq_bisimilarity 5 := by
  intro _ _ _ lts₁ lts₂ _
  exact funext fun _ => funext fun _ => propext (omegaBis OS le_rfl)
-- `Cslib.LTS.BisimilarityApprox.omega_eq_bisimilarity` idx 6: removable
theorem oe6 : drop% Cslib.LTS.BisimilarityApprox.omega_eq_bisimilarity 6 := by
  intro _ _ _ lts₁ lts₂ _
  exact funext fun _ => funext fun _ => propext (omegaBis OS' le_rfl)
-- `Cslib.LTS.BisimilarityApprox.eq_bisimilarity` idx 5: removable
theorem eb5 : drop% Cslib.LTS.BisimilarityApprox.eq_bisimilarity 5 := by
  intro _ _ _ lts₁ lts₂ _ o ho
  exact funext fun _ => funext fun _ => propext (omegaBis OS ho)
-- `Cslib.LTS.BisimilarityApprox.eq_bisimilarity` idx 6: removable
theorem eb6 : drop% Cslib.LTS.BisimilarityApprox.eq_bisimilarity 6 := by
  intro _ _ _ lts₁ lts₂ _ o ho
  exact funext fun _ => funext fun _ => propext (omegaBis OS' ho)
-- `Cslib.LTS.BisimilarityApprox.iff_bisimilarity` idx 7: removable
theorem ib7 : drop% Cslib.LTS.BisimilarityApprox.iff_bisimilarity 7 := by
  intro _ _ _ lts₁ lts₂ s₁ s₂ _ o ho
  exact omegaBis OS ho
-- `Cslib.LTS.BisimilarityApprox.iff_bisimilarity` idx 8: removable
theorem ib8 : drop% Cslib.LTS.BisimilarityApprox.iff_bisimilarity 8 := by
  intro _ _ _ lts₁ lts₂ s₁ s₂ _ o ho
  exact omegaBis OS' ho

-- `Cslib.LTS.BisimilarityApprox.follow_fst_omega` idx 10: necessary
theorem ffo10 : ¬ drop0% Cslib.LTS.BisimilarityApprox.follow_fst_omega 10 := fun h => by
  obtain ⟨t, ht, _⟩ := @h Unit Unit Unit LU LE0 () () () () inferInstance trivial
  exact ht
-- `Cslib.LTS.BisimilarityApprox.follow_fst_omega` idx 11: necessary
theorem ffo11 : ¬ drop0% Cslib.LTS.BisimilarityApprox.follow_fst_omega 11 := fun h => by
  obtain ⟨t, ht, _⟩ := @h Unit Unit Unit LE0 LE0 () () () () inferInstance
    (LTS.HomBisimilarityApprox.refl (lts := LE0) _ ())
  exact ht
-- `Cslib.LTS.BisimilarityApprox.follow_snd_omega` idx 10: necessary
theorem fso10 : ¬ drop0% Cslib.LTS.BisimilarityApprox.follow_snd_omega 10 := fun h => by
  obtain ⟨t, ht, _⟩ := @h Unit Unit Unit LE0 LU () () () () inferInstance trivial
  exact ht
-- `Cslib.LTS.BisimilarityApprox.follow_snd_omega` idx 11: necessary
theorem fso11 : ¬ drop0% Cslib.LTS.BisimilarityApprox.follow_snd_omega 11 := fun h => by
  obtain ⟨t, ht, _⟩ := @h Unit Unit Unit LE0 LE0 () () () () inferInstance
    (LTS.HomBisimilarityApprox.refl (lts := LE0) _ ())
  exact ht
-- `Cslib.LTS.BisimilarityApprox.bisimilarity_of_omega` idx 9: necessary
theorem bo9 : ¬ drop0% Cslib.LTS.BisimilarityApprox.bisimilarity_of_omega 9 := fun h =>
  nBis (@h Unit Unit Unit LU LE0 () () inferInstance inferInstance)
-- `Cslib.LTS.BisimilarityApprox.eq_bisimilarity` idx 8: necessary
theorem eb8' : ¬ drop0% Cslib.LTS.BisimilarityApprox.eq_bisimilarity 8 := fun h => by
  have e := @h Unit Unit Unit LU LE0 inferInstance inferInstance 0
  exact nBis (congrFun (congrFun e ()) () ▸ (by simp))
-- `Cslib.LTS.BisimilarityApprox.iff_bisimilarity` idx 10: necessary
theorem ib10 : ¬ drop0% Cslib.LTS.BisimilarityApprox.iff_bisimilarity 10 := fun h =>
  nBis ((@h Unit Unit Unit LU LE0 () () inferInstance inferInstance 0).1 (by simp))

-- `Cslib.LTS.BisimilarityApprox.follow_fst` idx 10: necessary
theorem ff10 : ¬ drop0% Cslib.LTS.BisimilarityApprox.follow_fst 10 := fun h => by
  obtain ⟨t, ht, _⟩ := @h Unit Unit Unit LU LE0 () () () () 0 trivial
  exact ht

-- `Cslib.LTS.BisimilarityApprox.follow_fst` idx 11: necessary
theorem ff11 : ¬ drop0% Cslib.LTS.BisimilarityApprox.follow_fst 11 := fun h => by
  obtain ⟨t, ht, _⟩ := @h Unit Unit Unit LE0 LE0 () () () () 0
    (LTS.HomBisimilarityApprox.refl (lts := LE0) _ ())
  exact ht

-- `Cslib.LTS.BisimilarityApprox.follow_snd` idx 10: necessary
theorem fs10 : ¬ drop0% Cslib.LTS.BisimilarityApprox.follow_snd 10 := fun h => by
  obtain ⟨t, ht, _⟩ := @h Unit Unit Unit LE0 LU () () () () 0 trivial
  exact ht

-- `Cslib.LTS.BisimilarityApprox.follow_snd` idx 11: necessary
theorem fs11 : ¬ drop0% Cslib.LTS.BisimilarityApprox.follow_snd 11 := fun h => by
  obtain ⟨t, ht, _⟩ := @h Unit Unit Unit LE0 LE0 () () () () 0
    (LTS.HomBisimilarityApprox.refl (lts := LE0) _ ())
  exact ht

-- `Cslib.LTS.BisimilarityApprox.of_ge` idx 9: necessary
theorem og9 : ¬ drop0% Cslib.LTS.BisimilarityApprox.of_ge 9 := fun h =>
  nA1 1 le_rfl (@h Unit Unit Unit LU LE0 () () 1 1 le_rfl)

-- `Cslib.LTS.BisimilarityApprox.of_ge` idx 10: necessary
theorem og10 : ¬ drop0% Cslib.LTS.BisimilarityApprox.of_ge 10 := fun h =>
  nA1 1 le_rfl (@h Unit Unit Unit LU LE0 () () 1 0 (by simp))

-- `Cslib.LTS.BisimilarityApprox.of_ge_nat` idx 9: necessary
theorem ogn9 : ¬ drop0% Cslib.LTS.BisimilarityApprox.of_ge_nat 9 := fun h =>
  nA1 _ (by simp) (@h Unit Unit Unit LU LE0 () () 1 1 le_rfl)

-- `Cslib.LTS.BisimilarityApprox.of_ge_nat` idx 10: necessary
theorem ogn10 : ¬ drop0% Cslib.LTS.BisimilarityApprox.of_ge_nat 10 := fun h =>
  nA1 _ (by simp) (@h Unit Unit Unit LU LE0 () () 1 0 (by simp))

-- `Cslib.LTS.BisimilarityApprox.limit_iff` idx 8: necessary
theorem li8 : ¬ drop0% Cslib.LTS.BisimilarityApprox.limit_iff 8 := fun h =>
  nA1 _ (by simp) ((@h Unit Unit Unit LU LE0 () () 1).2 (fun o' ho' => by
    have : o' = 0 := by simpa using ho'
    subst this; simp))

-- `Cslib.LTS.Bisimilarity.approx` idx 7: necessary
theorem ba7 : ¬ drop0% Cslib.LTS.Bisimilarity.approx 7 := fun h =>
  nA1 1 le_rfl (@h Unit Unit Unit LU LE0 () () 1)

-- `Cslib.LTS.BisimilarityApprox.eq_bisimilarity_of_le` idx 7: necessary
theorem eb7 : ¬ drop0% Cslib.LTS.BisimilarityApprox.eq_bisimilarity_of_le 7 := fun h => by
  have e := @h Unit Unit Unit LU LE0 1 0 (funext fun _ => funext fun _ => propext
    ⟨fun h => (nA1 1 le_rfl h).elim, fun h => (nBis h).elim⟩)
  have : LU.Bisimilarity LE0 () () := congrFun (congrFun e ()) () ▸ (by simp)
  exact nBis this

-- `Cslib.LTS.BisimilarityApprox.eq_bisimilarity_of_le` idx 8: necessary
theorem eb8 : ¬ drop0% Cslib.LTS.BisimilarityApprox.eq_bisimilarity_of_le 8 := fun h => by
  have e := @h Unit Unit Unit LU LE0 0 0 le_rfl
  have : LU.Bisimilarity LE0 () () := congrFun (congrFun e ()) () ▸ (by simp)
  exact nBis this

-- `Cslib.LTS.BisimilarityApprox.symm` idx 8: necessary
theorem sy8 : ¬ drop0% Cslib.LTS.BisimilarityApprox.symm 8 := fun h =>
  nA1 1 le_rfl (@h Unit 1 Unit Unit LU LE0 () ()).symm

-- `Cslib.LTS.BisimilarityApprox.trans` idx 11: necessary
theorem tr11 : ¬ drop0% Cslib.LTS.BisimilarityApprox.trans 11 := fun h =>
  nA1 1 le_rfl (@h Unit Unit Unit Unit LU LE0 LE0 () () () 1 (LTS.HomBisimilarityApprox.refl (lts := LE0) _ ()))

-- `Cslib.LTS.BisimilarityApprox.trans` idx 12: necessary
theorem tr12 : ¬ drop0% Cslib.LTS.BisimilarityApprox.trans 12 := fun h =>
  nA1 1 le_rfl (@h Unit Unit Unit Unit LU LU LE0 () () () 1 (LTS.HomBisimilarityApprox.refl (lts := LU) _ ()))

-- `Cslib.LTS.BisimilarityApprox.trans_nat` idx 11: necessary
theorem trn11 : ¬ drop0% Cslib.LTS.BisimilarityApprox.trans_nat 11 := fun h =>
  nA1 _ (by simp) (@h Unit Unit Unit LU LE0 () () Unit LE0 () 1 (LTS.HomBisimilarityApprox.refl (lts := LE0) _ ()))

-- `Cslib.LTS.BisimilarityApprox.trans_nat` idx 12: necessary
theorem trn12 : ¬ drop0% Cslib.LTS.BisimilarityApprox.trans_nat 12 := fun h =>
  nA1 _ (by simp) (@h Unit Unit Unit LU LU () () Unit LE0 () 1 (LTS.HomBisimilarityApprox.refl (lts := LU) _ ()))

-- `Cslib.LTS.BisimilarityApprox.trans_omega` idx 10: necessary
theorem tro10 : ¬ drop0% Cslib.LTS.BisimilarityApprox.trans_omega 10 := fun h =>
  nA1 _ (by simpa using Ordinal.one_lt_omega0.le) (@h Unit Unit Unit LU LE0 () () Unit LE0 () (LTS.HomBisimilarityApprox.refl (lts := LE0) _ ()))

-- `Cslib.LTS.BisimilarityApprox.trans_omega` idx 11: necessary
theorem tro11 : ¬ drop0% Cslib.LTS.BisimilarityApprox.trans_omega 11 := fun h =>
  nA1 _ (by simpa using Ordinal.one_lt_omega0.le) (@h Unit Unit Unit LU LU () () Unit LE0 () (LTS.HomBisimilarityApprox.refl (lts := LU) _ ()))


open Cslib LTS
namespace U1c0
inductive St | r | c (m k : ℕ) | d (j : ℕ)
open St
/-- Image-infinite LTS: r -a-> c m m; c m (k+1) -b-> c m k; d j -b-> d (j+1). -/
def T2 : St → Bool → St → Prop
  | .r, false, .c m k => k = m
  | .c m (k+1), true, t => t = .c m k
  | .d j, true, t => t = .d (j+1)
  | _, _, _ => False
/-- L2 plus r -a-> d 0. -/
def L2 : LTS St Bool := ⟨T2⟩
def L1 : LTS St Bool := ⟨fun s l t => T2 s l t ∨ (s = .r ∧ l = false ∧ t = .d 0)⟩

theorem cc (m : ℕ) : ∀ n k, L1.BisimilarityApprox L2 (n : ℕ) (c m k) (c m k) := by
  intro n
  induction n with
  | zero => intro k; simp
  | succ n ih =>
    intro k
    have : L1.BisimilarityApprox L2 ((n : WithTop Ordinal) + 1) (c m k) (c m k) := by
      rw [BisimilarityApprox.succ_iff]
      intro μ
      cases k with
      | zero =>
        constructor
        · rintro t (h | h) <;> simp [L1, L2, T2] at h <;> cases μ <;> simp [T2] at h
        · rintro t h; cases μ <;> simp [L2, T2] at h
      | succ k =>
        constructor
        · rintro t (h | ⟨h1, _⟩)
          · cases μ <;> simp [T2] at h
            subst h; exact ⟨_, by simp [L2, T2], ih k⟩
          · cases h1
        · rintro t h
          cases μ <;> simp [L2, T2] at h
          subst h; exact ⟨_, Or.inl (by simp [T2]), ih k⟩
    simpa using this

theorem dc (m : ℕ) : ∀ n k j, n ≤ k → L1.BisimilarityApprox L2 (n : ℕ) (d j) (c m k) := by
  intro n
  induction n with
  | zero => intro k j _; simp
  | succ n ih =>
    intro k j hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have : L1.BisimilarityApprox L2 ((n : WithTop Ordinal) + 1) (d j) (c m (k+1)) := by
      rw [BisimilarityApprox.succ_iff]
      intro μ
      constructor
      · rintro t (h | ⟨h1, _⟩)
        · cases μ <;> simp [T2] at h
          subst h; exact ⟨c m k, by simp [L2, T2], ih k (j+1) (by omega)⟩
        · cases h1
      · rintro t h
        cases μ <;> simp [L2, T2] at h
        subst h; exact ⟨d (j+1), Or.inl (by simp [T2]), ih k (j+1) (by omega)⟩
    simpa using this

theorem rr : L1.BisimilarityApprox L2 (Ordinal.omega0 : Ordinal) r r := by
  rw [BisimilarityApprox.omega_iff]
  intro n
  cases n with
  | zero => simp
  | succ n =>
    have : L1.BisimilarityApprox L2 ((n : WithTop Ordinal) + 1) r r := by
      rw [BisimilarityApprox.succ_iff]
      intro μ
      constructor
      · rintro t (h | ⟨_, h2, h3⟩)
        · cases μ <;> cases t <;> simp [T2] at h
          subst h; exact ⟨_, by simp [L2, T2], cc _ _ _⟩
        · subst h2 h3
          exact ⟨.c n n, by simp [L2, T2], dc n n n 0 le_rfl⟩
      · rintro t h
        cases μ <;> cases t <;> simp [L2, T2] at h
        subst h; exact ⟨_, Or.inl (by simp [T2]), cc _ _ _⟩
    simpa using this

theorem dcn (m : ℕ) : ∀ k n j, L1.BisimilarityApprox L2 (n : ℕ) (d j) (c m k) → n ≤ k := by
  intro k
  induction k with
  | zero =>
    intro n j h
    cases n with
    | zero => rfl
    | succ n =>
      have h' : L1.BisimilarityApprox L2 ((n : WithTop Ordinal) + 1) (d j) (c m 0) := by simpa using h
      obtain ⟨t, ht, _⟩ := h'.follow_fst (μ := true) (s₁' := d (j+1)) (Or.inl (by simp [T2]))
      simp [L2, T2] at ht
  | succ k ih =>
    intro n j h
    cases n with
    | zero => omega
    | succ n =>
      have h' : L1.BisimilarityApprox L2 ((n : WithTop Ordinal) + 1) (d j) (c m (k+1)) := by simpa using h
      obtain ⟨t, ht, hr⟩ := h'.follow_fst (μ := true) (s₁' := d (j+1)) (Or.inl (by simp [T2]))
      simp [L2, T2] at ht; subst ht
      have := ih n _ (by simpa using hr)
      omega

theorem noMatch (t : St) (ht : L2.Tr r false t) :
    ¬ L1.BisimilarityApprox L2 (Ordinal.omega0 : Ordinal) (d 0) t := by
  cases t <;> simp [L2, T2] at ht
  rename_i m k
  subst ht
  intro h
  have := dcn k k (k+1) 0 (BisimilarityApprox.omega_iff.mp h (k+1))
  omega
end U1c0
open U1c0

-- `Cslib.LTS.BisimilarityApprox.isSimulation_omega` idx 5: necessary
theorem iso5 : ¬ drop0% Cslib.LTS.BisimilarityApprox.isSimulation_omega 5 := fun h => by
  obtain ⟨t, ht, hr⟩ := @h St St Bool L1 L2 St.r St.r rr false (St.d 0) (Or.inr ⟨rfl, rfl, rfl⟩)
  exact noMatch t ht hr

-- `Cslib.LTS.BisimilarityApprox.flip_isSimulation_omega` idx 5: necessary
theorem fio5 : ¬ drop0% Cslib.LTS.BisimilarityApprox.flip_isSimulation_omega 5 := fun h => by
  obtain ⟨t, ht, hr⟩ := @h St St Bool L2 L1 St.r St.r rr.symm false (St.d 0) (Or.inr ⟨rfl, rfl, rfl⟩)
  exact noMatch t ht hr.symm

-- `Cslib.LTS.BisimilarityApprox.follow_fst_omega` idx 9: necessary
theorem ffo9 : ¬ drop0% Cslib.LTS.BisimilarityApprox.follow_fst_omega 9 := fun h => by
  obtain ⟨t, ht, hr⟩ := @h St St Bool L1 L2 St.r St.r false (St.d 0) rr (Or.inr ⟨rfl, rfl, rfl⟩)
  exact noMatch t ht hr

-- `Cslib.LTS.BisimilarityApprox.follow_snd_omega` idx 9: necessary
theorem fso9 : ¬ drop0% Cslib.LTS.BisimilarityApprox.follow_snd_omega 9 := fun h => by
  obtain ⟨t, ht, hr⟩ := @h St St Bool L2 L1 St.r St.r false (St.d 0) rr.symm (Or.inr ⟨rfl, rfl, rfl⟩)
  exact noMatch t ht hr.symm
