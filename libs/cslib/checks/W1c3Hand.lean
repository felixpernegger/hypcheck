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

namespace W1c3
open Cslib Cslib.LTS

def LU : LTS Unit Unit := ⟨fun _ _ _ => True⟩
def LE0 : LTS Unit Unit := ⟨fun _ _ _ => False⟩
def LB : LTS Bool Unit := ⟨fun s _ t => s = false ∧ t = true⟩
def LBT : LTS Bool Unit := ⟨fun _ _ _ => True⟩
def LNT : LTS ℕ Unit := ⟨fun _ _ _ => True⟩
def LUN : LTS Unit ℕ := ⟨fun _ _ _ => True⟩
def LN0 : LTS ℕ Unit := ⟨fun _ _ _ => False⟩

instance LBdet : LB.Deterministic := ⟨fun _ _ _ _ ha hb => ha.2.trans hb.2.symm⟩

theorem eqBis {S L : Type} (l : LTS S L) : l.IsBisimulation l Eq := by
  rintro s _ rfl μ; exact ⟨fun s' h => ⟨s', h, rfl⟩, fun s' h => ⟨s', h, rfl⟩⟩
theorem botBis {S1 S2 L : Type} (l1 : LTS S1 L) (l2 : LTS S2 L) :
    l1.IsBisimulation l2 (fun _ _ => False) := fun _ _ h => h.elim
theorem e0Bis : LE0.IsBisimulation LE0 (fun _ _ => True) :=
  fun _ _ _ _ => ⟨fun _ h => h.elim, fun _ h => h.elim⟩
theorem notBisUE (r : Unit → Unit → Prop) (hb : LU.IsBisimulation LE0 r) (hr : r () ()) : False := by
  obtain ⟨_, h, _⟩ := (hb hr ()).1 () trivial; exact h
theorem notBisEU (r : Unit → Unit → Prop) (hb : LE0.IsBisimulation LU r) (hr : r () ()) : False := by
  obtain ⟨_, h, _⟩ := (hb hr ()).2 () trivial; exact h
theorem notBisimUE : ¬ LU.Bisimilarity LE0 () () := fun ⟨r, hr, hb⟩ => notBisUE r hb hr
theorem notBisimEU : ¬ LE0.Bisimilarity LU () () := fun ⟨r, hr, hb⟩ => notBisEU r hb hr
theorem notSimUE : ¬ LU.Similarity LE0 () () := fun ⟨_, hr, hs⟩ => by
  obtain ⟨_, h, _⟩ := hs hr () () trivial; exact h
theorem notTEUE : ¬ LU.TraceEq LE0 () () := fun h => by
  have : [()] ∈ LU.traces () := ⟨(), .single _ trivial⟩
  rw [h] at this
  obtain ⟨_, h'⟩ := this
  cases h' with | stepL h _ => exact h
theorem notBisLB : ¬ LB.Bisimilarity LB false true := fun h => by
  obtain ⟨_, h, _⟩ := LTS.Bisimilarity.follow_fst (μ := ()) (s₁' := true) h ⟨rfl, rfl⟩
  exact absurd h.1 (by decide)
theorem notFinLNT : ¬ Finite (LNT.image 0 ()) := fun hf => by
  have himg : LNT.image 0 () = Set.univ := Set.eq_univ_of_forall fun _ => trivial
  have := Set.finite_coe_iff.mp hf
  rw [himg] at this
  exact Set.infinite_univ this
theorem notFinLUN : ¬ Finite (LUN.outgoingLabels ()) := fun hf => by
  have himg : LUN.outgoingLabels () = Set.univ := Set.eq_univ_of_forall fun _ => ⟨(), trivial⟩
  have := Set.finite_coe_iff.mp hf
  rw [himg] at this
  exact Set.infinite_univ this

-- 0 → 1, 0 → 2, 1 → 3 (nondeterministic) vs 0 → 1 → 2 (deterministic): trace equivalent at 0, not bisimilar
def LD1 : LTS ℕ Unit := ⟨fun s _ t => (s = 0 ∧ (t = 1 ∨ t = 2)) ∨ (s = 1 ∧ t = 3)⟩
def LD2 : LTS ℕ Unit := ⟨fun s _ t => (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 2)⟩
instance LD2det : LD2.Deterministic := ⟨fun _ _ _ _ ha hb => by simp only [LD2] at ha hb; omega⟩

theorem te12 : LD1.TraceEq LD2 0 0 := by
  ext μs
  rcases μs with _ | ⟨_, _ | ⟨_, _ | ⟨_, μs⟩⟩⟩ <;>
    simp [LTS.mem_traces_iff, LTS.MTr.cons_iff, LD1, LD2]


theorem notBisD12 : ¬ LD1.Bisimilarity LD2 0 0 := fun h => by
  obtain ⟨s, hs, h2⟩ := LTS.Bisimilarity.follow_fst (μ := ()) (s₁' := 2) h (by simp [LD1])
  have : s = 1 := by simp [LD2] at hs; omega
  subst this
  obtain ⟨_, h3, _⟩ := LTS.Bisimilarity.follow_snd (μ := ()) (s₂' := 2) h2 (by simp [LD2])
  simp [LD1] at h3
theorem notBisD21 : ¬ LD2.Bisimilarity LD1 0 0 := fun h => by
  obtain ⟨s, hs, h2⟩ := LTS.Bisimilarity.follow_snd (μ := ()) (s₂' := 2) h (by simp [LD1])
  have : s = 1 := by simp [LD2] at hs; omega
  subst this
  obtain ⟨_, h3, _⟩ := LTS.Bisimilarity.follow_fst (μ := ()) (s₁' := 2) h2 (by simp [LD2])
  simp [LD1] at h3

-- ===== LTS.Basic =====

-- `Cslib.LTS.ext` idx 4: necessary (LU ≠ LE0)
theorem ext4 : ¬ drop0% Cslib.LTS.ext 4 := fun H => by
  have := congrArg (fun l => l.Tr () () ()) (H (x := LU) (y := LE0))
  simp [LU, LE0] at this

-- `Cslib.LTS.MTr.stepR` idx 8: necessary (single edge false → true, s1 = true, μs = [])
theorem stepR8 : ¬ drop0% Cslib.LTS.MTr.stepR 8 := fun H => by
  have := H LB (s1 := true) (μs := []) (s2 := false) (μ := ()) (s3 := true) ⟨rfl, rfl⟩
  simp [LB] at this

-- `Cslib.LTS.mtrInv_of_trInv` idx 4: necessary (single edge false → true, p = (· = false))
theorem mtrInv4 : ¬ drop0% Cslib.LTS.mtrInv_of_trInv 4 := fun H =>
  absurd (H (lts := LB) (p := fun s => s = false) false [()] true (.single _ ⟨rfl, rfl⟩) rfl) (by decide)

-- `Cslib.LTS.traces_in` idx 6: necessary (empty LTS, μs = [()])
theorem tracesIn6 : ¬ drop0% Cslib.LTS.traces_in 6 := fun H => by
  obtain ⟨_, hs⟩ := H (s := ()) (μs := [()]) (s' := ()) (lts := LE0)
  cases hs with | stepL h _ => exact h

-- `Cslib.LTS.DeterministicStateLabel.subsingleton_image` idx 5: necessary (total LTS on Bool)
theorem dslSub5 : ¬ drop0% Cslib.LTS.DeterministicStateLabel.subsingleton_image 5 := fun H =>
  absurd (H (s := false) (μ := ()) (lts := LBT) (show true ∈ LBT.image false () from trivial)
    (show false ∈ LBT.image false () from trivial)) (by decide)

-- `Cslib.LTS.DeterministicState.subsingleton_image` idx 4: necessary (total LTS on Bool)
theorem dsSub4 : ¬ drop0% Cslib.LTS.DeterministicState.subsingleton_image 4 := fun H =>
  absurd (H (s := false) (lts := LBT) () (show true ∈ LBT.image false () from trivial)
    (show false ∈ LBT.image false () from trivial)) (by decide)

-- `Cslib.LTS.Deterministic.subsingleton_image` idx 3: necessary (total LTS on Bool)
theorem detSub3 : ¬ drop0% Cslib.LTS.Deterministic.subsingleton_image 3 := fun H =>
  absurd (H (lts := LBT) false () (show true ∈ LBT.image false () from trivial)
    (show false ∈ LBT.image false () from trivial)) (by decide)

-- `Cslib.LTS.Deterministic.eq_of_tr` idx 8: necessary (single edge false → true, s2 = false)
theorem eqTr8 : ¬ drop0% Cslib.LTS.Deterministic.eq_of_tr 8 := fun H =>
  absurd (H (s1 := false) (μ := ()) (s2 := false) (s2' := true) (lts := LB) ⟨rfl, rfl⟩) (by decide)

-- `Cslib.LTS.Deterministic.eq_of_tr` idx 9: necessary (single edge false → true, s2' = false)
theorem eqTr9 : ¬ drop0% Cslib.LTS.Deterministic.eq_of_tr 9 := fun H =>
  absurd (H (s1 := false) (μ := ()) (s2 := true) (s2' := false) (lts := LB) ⟨rfl, rfl⟩) (by decide)

-- `Cslib.LTS.Deterministic.eq_of_mTr` idx 8: necessary (single edge false → true, s2 = false)
theorem eqMTr8 : ¬ drop0% Cslib.LTS.Deterministic.eq_of_mTr 8 := fun H =>
  absurd (H (s1 := false) (μs := [()]) (s2 := false) (s2' := true) (lts := LB) (.single _ ⟨rfl, rfl⟩))
    (by decide)

-- `Cslib.LTS.Deterministic.eq_of_mTr` idx 9: necessary (single edge false → true, s2' = false)
theorem eqMTr9 : ¬ drop0% Cslib.LTS.Deterministic.eq_of_mTr 9 := fun H =>
  absurd (H (s1 := false) (μs := [()]) (s2 := true) (s2' := false) (lts := LB) (.single _ ⟨rfl, rfl⟩))
    (by decide)

-- `Cslib.LTS.DeterministicStateLabel.not_tr_of_ne` idx 8: necessary (s₁ = s₂ = true)
theorem notTr8 : ¬ drop0% Cslib.LTS.DeterministicStateLabel.not_tr_of_ne 8 := fun H =>
  H LB (s := false) (μ := ()) (s₁ := true) (s₂ := true) (LBdet.deterministic false ()) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩

-- `Cslib.LTS.DeterministicStateLabel.not_tr_of_ne` idx 9: necessary (s₁ = false, s₂ = true)
theorem notTr9 : ¬ drop0% Cslib.LTS.DeterministicStateLabel.not_tr_of_ne 9 := fun H =>
  H LB (s := false) (μ := ()) (s₁ := false) (s₂ := true) (LBdet.deterministic false ()) (by decide) ⟨rfl, rfl⟩

-- `Cslib.LTS.DeterministicStateLabel.image_singleton_iff_tr` idx 6: necessary (total LTS on Bool)
theorem imgSing6 : ¬ drop0% Cslib.LTS.DeterministicStateLabel.image_singleton_iff_tr 6 := fun H => by
  have := (H LBT (s := false) (μ := ()) (s' := true)).2 trivial
  have h2 : false ∈ LBT.image false () := trivial
  rw [this] at h2
  simp at h2

-- `Cslib.LTS.DeterministicStateLabel.image_char` idx 5: necessary (total LTS on Bool)
theorem imgChar5 : ¬ drop0% Cslib.LTS.DeterministicStateLabel.image_char 5 := fun H => by
  have a : true ∈ LBT.image false () := trivial
  have b : false ∈ LBT.image false () := trivial
  rcases H LBT (s := false) (μ := ()) with ⟨s', hs⟩ | hs
  · rw [hs] at a b
    simp only [Set.mem_singleton_iff] at a b
    subst a
    exact absurd b (by decide)
  · rw [hs] at a
    exact a

-- `Cslib.LTS.DeterministicStateLabel.finite_image` idx 5: necessary (total LTS on ℕ)
theorem finImg5 : ¬ drop0% Cslib.LTS.DeterministicStateLabel.finite_image 5 := fun H =>
  notFinLNT (H LNT (s := 0) (μ := ()))

-- `Cslib.LTS.instFiniteElemImageOfDeterministic` idx 3: necessary (total LTS on ℕ)
theorem instFin3 : ¬ drop0% Cslib.LTS.instFiniteElemImageOfDeterministic 3 := fun H =>
  notFinLNT (H LNT 0 ())

-- `Cslib.LTS.deterministic_imageFinite` idx 3: necessary (total LTS on ℕ)
theorem detImgFin3 : ¬ drop0% Cslib.LTS.deterministic_imageFinite 3 := fun H =>
  notFinLNT (H LNT 0 ())

-- `Cslib.LTS.finiteState_imageFinite` idx 3: necessary (total LTS on ℕ)
theorem fsImgFin3 : ¬ drop0% Cslib.LTS.finiteState_imageFinite 3 := fun H =>
  notFinLNT (H LNT 0 ())

-- `Cslib.LTS.FinitelyBranching.image_finite` idx 3: necessary (total LTS on ℕ)
theorem fbImg3 : ¬ drop0% Cslib.LTS.FinitelyBranching.image_finite 3 := fun H =>
  notFinLNT (H (lts := LNT) 0 ())

-- `Cslib.LTS.FinitelyBranching.finite_state` idx 3: necessary (total LTS with labels ℕ)
theorem fbFs3 : ¬ drop0% Cslib.LTS.FinitelyBranching.finite_state 3 := fun H =>
  notFinLUN (H (lts := LUN) ())

-- `Cslib.LTS.FinitelyBranching.of_finite` idx 3: necessary (total LTS on ℕ, labels Unit)
theorem fbOf3 : ¬ drop0% Cslib.LTS.FinitelyBranching.of_finite 3 := fun H =>
  notFinLNT (@LTS.FinitelyBranching.image_finite _ _ LNT (H LNT) 0 ())

-- `Cslib.LTS.FinitelyBranching.of_finite` idx 4: necessary (total LTS on Unit, labels ℕ)
theorem fbOf4 : ¬ drop0% Cslib.LTS.FinitelyBranching.of_finite 4 := fun H =>
  notFinLUN (@LTS.FinitelyBranching.finite_state _ _ LUN (H LUN) ())

-- `Cslib.LTS.Terminating.terminating` idx 3: necessary (one state with a self-loop)
theorem term3 : ¬ drop0% Cslib.LTS.Terminating.terminating 3 := fun H => by
  have key : ∀ x, Acc (fun a b => LU.UnlabelledTr b a) x → False := fun x hx => by
    induction hx with
    | intro x _ ih => exact ih x ⟨(), trivial⟩
  exact key () ((H (lts := LU)).apply ())

-- `Cslib.LTS.Acyclic.acyclic` idx 3: necessary (one state with a self-loop)
theorem acyc3 : ¬ drop0% Cslib.LTS.Acyclic.acyclic 3 := fun H =>
  (H (lts := LU)).irrefl () (.single ⟨(), trivial⟩)

-- `Cslib.LTS.Deterministic.traces_of_mTr` idx 7: necessary (single edge false → true, s = true, μs = [()])
theorem trMTr7 : ¬ drop0% Cslib.LTS.Deterministic.traces_of_mTr 7 := fun H => by
  have := H (s := true) (μs := [()]) (s' := false) (lts := LB)
  have h1 : ([] : List Unit) ∈ LB.traces false := ⟨false, .refl⟩
  rw [this] at h1
  obtain ⟨_, h2⟩ := h1
  simp [LB] at h2

-- `Cslib.LTS.Deterministic.traces_of_tr` idx 7: necessary (single edge false → true, s = true)
theorem trTr7 : ¬ drop0% Cslib.LTS.Deterministic.traces_of_tr 7 := fun H => by
  have := H (s := true) (μ := ()) (s' := false) (lts := LB)
  have h1 : ([] : List Unit) ∈ LB.traces false := ⟨false, .refl⟩
  rw [this] at h1
  obtain ⟨_, h2⟩ := h1
  simp [LB] at h2


-- ===== LTS.Bisimulation =====

-- `Cslib.LTS.IsBisimulation.follow_fst` idx 11: necessary (empty bisimulation, LU vs LE0)
theorem ff11 : ¬ drop0% Cslib.LTS.IsBisimulation.follow_fst 11 := fun H => by
  obtain ⟨_, h, _⟩ := H (lts₁ := LU) (lts₂ := LE0) (r := fun _ _ => False) (s₁ := ()) (s₂ := ()) (μ := ())
    (s₁' := ()) (botBis _ _) trivial
  exact h

-- `Cslib.LTS.IsBisimulation.follow_fst` idx 12: necessary (empty LTSs, total relation)
theorem ff12 : ¬ drop0% Cslib.LTS.IsBisimulation.follow_fst 12 := fun H => by
  obtain ⟨_, h, _⟩ := H (lts₁ := LE0) (lts₂ := LE0) (r := fun _ _ => True) (s₁ := ()) (s₂ := ()) (μ := ())
    (s₁' := ()) e0Bis trivial
  exact h

-- `Cslib.LTS.IsBisimulation.follow_snd` idx 11: necessary (empty bisimulation, LE0 vs LU)
theorem fs11 : ¬ drop0% Cslib.LTS.IsBisimulation.follow_snd 11 := fun H => by
  obtain ⟨_, h, _⟩ := H (lts₁ := LE0) (lts₂ := LU) (r := fun _ _ => False) (s₁ := ()) (s₂ := ()) (μ := ())
    (s₂' := ()) (botBis _ _) trivial
  exact h

-- `Cslib.LTS.IsBisimulation.follow_snd` idx 12: necessary (empty LTSs, total relation)
theorem fs12 : ¬ drop0% Cslib.LTS.IsBisimulation.follow_snd 12 := fun H => by
  obtain ⟨_, h, _⟩ := H (lts₁ := LE0) (lts₂ := LE0) (r := fun _ _ => True) (s₁ := ()) (s₂ := ()) (μ := ())
    (s₂' := ()) e0Bis trivial
  exact h

-- `Cslib.LTS.IsBisimulation.match_deterministic` idx 11: necessary (r relates only false,false; edge false → true)
theorem md11 : ¬ drop0% Cslib.LTS.IsBisimulation.match_deterministic 11 := fun H =>
  absurd (H (lts₁ := LB) (lts₂ := LB) (r := fun a b => a = false ∧ b = false) (s₁ := false) (s₂ := false)
    (μ := ()) (s₁' := true) (s₂' := true) ⟨rfl, rfl⟩ (LBdet.deterministic false ()) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩).1
    (by decide)

-- `Cslib.LTS.IsBisimulation.match_deterministic` idx 13: necessary (total LTS on Bool, r = Eq)
theorem md13 : ¬ drop0% Cslib.LTS.IsBisimulation.match_deterministic 13 := fun H =>
  absurd (H (lts₁ := LBT) (lts₂ := LBT) (r := Eq) (s₁ := false) (s₂ := false) (μ := ()) (s₁' := true)
    (s₂' := false) (eqBis _) rfl trivial trivial) (by decide)

-- `Cslib.LTS.IsBisimulation.match_deterministic` idx 14: necessary (r = Eq, s₁' = false, s₂' = true)
theorem md14 : ¬ drop0% Cslib.LTS.IsBisimulation.match_deterministic 14 := fun H =>
  absurd (H (lts₁ := LB) (lts₂ := LB) (r := Eq) (s₁ := false) (s₂ := false) (μ := ()) (s₁' := false)
    (s₂' := true) (eqBis _) rfl (LBdet.deterministic false ()) ⟨rfl, rfl⟩) (by decide)

-- `Cslib.LTS.IsBisimulation.match_deterministic` idx 15: necessary (r = Eq, s₁' = true, s₂' = false)
theorem md15 : ¬ drop0% Cslib.LTS.IsBisimulation.match_deterministic 15 := fun H =>
  absurd (H (lts₁ := LB) (lts₂ := LB) (r := Eq) (s₁ := false) (s₂ := false) (μ := ()) (s₁' := true)
    (s₂' := false) (eqBis _) rfl (LBdet.deterministic false ()) ⟨rfl, rfl⟩) (by decide)

-- `Cslib.LTS.IsBisimulation.match_deterministic₂` idx 11: necessary (r relates only false,false; edge false → true)
theorem mdd11 : ¬ drop0% Cslib.LTS.IsBisimulation.match_deterministic₂ 11 := fun H =>
  absurd (H (lts₁ := LB) (lts₂ := LB) (r := fun a b => a = false ∧ b = false) (s₁ := false) (s₂ := false)
    (μ := ()) (s₁' := true) (s₂' := true) ⟨rfl, rfl⟩ (LBdet.deterministic false ()) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩).1
    (by decide)

-- `Cslib.LTS.IsBisimulation.match_deterministic₂` idx 12: necessary (empty bisimulation)
theorem mdd12 : ¬ drop0% Cslib.LTS.IsBisimulation.match_deterministic₂ 12 := fun H =>
  H (lts₁ := LU) (lts₂ := LU) (r := fun _ _ => False) (s₁ := ()) (s₂ := ()) (μ := ()) (s₁' := ())
    (s₂' := ()) (botBis _ _) (fun _ _ _ _ => rfl) trivial trivial

-- `Cslib.LTS.IsBisimulation.match_deterministic₂` idx 13: necessary (total LTS on Bool, r = Eq)
theorem mdd13 : ¬ drop0% Cslib.LTS.IsBisimulation.match_deterministic₂ 13 := fun H =>
  absurd (H (lts₁ := LBT) (lts₂ := LBT) (r := Eq) (s₁ := false) (s₂ := false) (μ := ()) (s₁' := true)
    (s₂' := false) (eqBis _) rfl trivial trivial) (by decide)

-- `Cslib.LTS.IsBisimulation.match_deterministic₂` idx 14: necessary (r = Eq, s₁' = false, s₂' = true)
theorem mdd14 : ¬ drop0% Cslib.LTS.IsBisimulation.match_deterministic₂ 14 := fun H =>
  absurd (H (lts₁ := LB) (lts₂ := LB) (r := Eq) (s₁ := false) (s₂ := false) (μ := ()) (s₁' := false)
    (s₂' := true) (eqBis _) rfl (LBdet.deterministic false ()) ⟨rfl, rfl⟩) (by decide)

-- `Cslib.LTS.IsBisimulation.match_deterministic₂` idx 15: necessary (r = Eq, s₁' = true, s₂' = false)
theorem mdd15 : ¬ drop0% Cslib.LTS.IsBisimulation.match_deterministic₂ 15 := fun H =>
  absurd (H (lts₁ := LB) (lts₂ := LB) (r := Eq) (s₁ := false) (s₂ := false) (μ := ()) (s₁' := true)
    (s₂' := false) (eqBis _) rfl (LBdet.deterministic false ()) ⟨rfl, rfl⟩) (by decide)

-- `Cslib.LTS.IsBisimulation.follow_fst_deterministic` idx 10: necessary (total relation, LU vs LE0)
theorem ffd10 : ¬ drop0% Cslib.LTS.IsBisimulation.follow_fst_deterministic 10 := fun H => by
  obtain ⟨_, ⟨h, _⟩, _⟩ := H (lts₁ := LU) (lts₂ := LE0) (r := fun _ _ => True) (s₁ := ()) (s₂ := ())
    (μ := ()) (s₁' := ()) trivial (fun _ _ h _ => h.elim) trivial
  exact h

-- `Cslib.LTS.IsBisimulation.follow_fst_deterministic` idx 11: necessary (empty bisimulation, LU vs LE0)
theorem ffd11 : ¬ drop0% Cslib.LTS.IsBisimulation.follow_fst_deterministic 11 := fun H => by
  obtain ⟨_, ⟨h, _⟩, _⟩ := H (lts₁ := LU) (lts₂ := LE0) (r := fun _ _ => False) (s₁ := ()) (s₂ := ())
    (μ := ()) (s₁' := ()) (botBis _ _) (fun _ _ h _ => h.elim) trivial
  exact h

-- `Cslib.LTS.IsBisimulation.follow_fst_deterministic` idx 12: necessary (total LTS on Bool, total relation)
theorem ffd12 : ¬ drop0% Cslib.LTS.IsBisimulation.follow_fst_deterministic 12 := fun H => by
  obtain ⟨_, _, hu⟩ := H (lts₁ := LBT) (lts₂ := LBT) (r := fun _ _ => True) (s₁ := false) (s₂ := false)
    (μ := ()) (s₁' := false) (fun _ _ _ _ => ⟨fun s _ => ⟨s, trivial, trivial⟩, fun s _ => ⟨s, trivial, trivial⟩⟩)
    trivial trivial
  exact absurd ((hu true ⟨trivial, trivial⟩).trans (hu false ⟨trivial, trivial⟩).symm) (by decide)

-- `Cslib.LTS.IsBisimulation.follow_fst_deterministic` idx 13: necessary (empty LTSs, total relation)
theorem ffd13 : ¬ drop0% Cslib.LTS.IsBisimulation.follow_fst_deterministic 13 := fun H => by
  obtain ⟨_, ⟨h, _⟩, _⟩ := H (lts₁ := LE0) (lts₂ := LE0) (r := fun _ _ => True) (s₁ := ()) (s₂ := ())
    (μ := ()) (s₁' := ()) e0Bis trivial (fun _ _ h _ => h.elim)
  exact h

-- `Cslib.LTS.IsBisimulation.follow_snd_deterministic` idx 10: necessary (total relation, LE0 vs LU)
theorem fsd10 : ¬ drop0% Cslib.LTS.IsBisimulation.follow_snd_deterministic 10 := fun H => by
  obtain ⟨_, ⟨h, _⟩, _⟩ := H (lts₁ := LE0) (lts₂ := LU) (r := fun _ _ => True) (s₁ := ()) (s₂ := ())
    (μ := ()) (s₂' := ()) trivial (fun _ _ h _ => h.elim) trivial
  exact h

-- `Cslib.LTS.IsBisimulation.follow_snd_deterministic` idx 11: necessary (empty bisimulation, LE0 vs LU)
theorem fsd11 : ¬ drop0% Cslib.LTS.IsBisimulation.follow_snd_deterministic 11 := fun H => by
  obtain ⟨_, ⟨h, _⟩, _⟩ := H (lts₁ := LE0) (lts₂ := LU) (r := fun _ _ => False) (s₁ := ()) (s₂ := ())
    (μ := ()) (s₂' := ()) (botBis _ _) (fun _ _ h _ => h.elim) trivial
  exact h

-- `Cslib.LTS.IsBisimulation.follow_snd_deterministic` idx 12: necessary (total LTS on Bool, total relation)
theorem fsd12 : ¬ drop0% Cslib.LTS.IsBisimulation.follow_snd_deterministic 12 := fun H => by
  obtain ⟨_, _, hu⟩ := H (lts₁ := LBT) (lts₂ := LBT) (r := fun _ _ => True) (s₁ := false) (s₂ := false)
    (μ := ()) (s₂' := false) (fun _ _ _ _ => ⟨fun s _ => ⟨s, trivial, trivial⟩, fun s _ => ⟨s, trivial, trivial⟩⟩)
    trivial trivial
  exact absurd ((hu true ⟨trivial, trivial⟩).trans (hu false ⟨trivial, trivial⟩).symm) (by decide)

-- `Cslib.LTS.IsBisimulation.follow_snd_deterministic` idx 13: necessary (empty LTSs, total relation)
theorem fsd13 : ¬ drop0% Cslib.LTS.IsBisimulation.follow_snd_deterministic 13 := fun H => by
  obtain ⟨_, ⟨h, _⟩, _⟩ := H (lts₁ := LE0) (lts₂ := LE0) (r := fun _ _ => True) (s₁ := ()) (s₂ := ())
    (μ := ()) (s₂' := ()) e0Bis trivial (fun _ _ h _ => h.elim)
  exact h

-- `Cslib.LTS.Bisimilarity.follow_fst` idx 9: necessary (LU vs LE0)
theorem bff9 : ¬ drop0% Cslib.LTS.Bisimilarity.follow_fst 9 := fun H => by
  obtain ⟨_, h, _⟩ := H (lts₁ := LU) (lts₂ := LE0) (s₁ := ()) (s₂ := ()) (μ := ()) (s₁' := ()) trivial
  exact h

-- `Cslib.LTS.Bisimilarity.follow_fst` idx 10: necessary (empty LTSs)
theorem bff10 : ¬ drop0% Cslib.LTS.Bisimilarity.follow_fst 10 := fun H => by
  obtain ⟨_, h, _⟩ := H (lts₁ := LE0) (lts₂ := LE0) (s₁ := ()) (s₂ := ()) (μ := ()) (s₁' := ())
    ⟨_, trivial, e0Bis⟩
  exact h

-- `Cslib.LTS.Bisimilarity.follow_snd` idx 9: necessary (LE0 vs LU)
theorem bfs9 : ¬ drop0% Cslib.LTS.Bisimilarity.follow_snd 9 := fun H => by
  obtain ⟨_, h, _⟩ := H (lts₁ := LE0) (lts₂ := LU) (s₁ := ()) (s₂ := ()) (μ := ()) (s₂' := ()) trivial
  exact h

-- `Cslib.LTS.Bisimilarity.follow_snd` idx 10: necessary (empty LTSs)
theorem bfs10 : ¬ drop0% Cslib.LTS.Bisimilarity.follow_snd 10 := fun H => by
  obtain ⟨_, h, _⟩ := H (lts₁ := LE0) (lts₂ := LE0) (s₁ := ()) (s₂ := ()) (μ := ()) (s₂' := ())
    ⟨_, trivial, e0Bis⟩
  exact h

-- `Cslib.LTS.HomBisimilarity.of_image_eq` idx 5: necessary (edge false → true; false, true not bisimilar)
theorem hbImg5 : ¬ drop0% Cslib.LTS.HomBisimilarity.of_image_eq 5 := fun H =>
  notBisLB (H (lts := LB) (s₁ := false) (s₂ := true))

-- `Cslib.LTS.IsBisimulation.inv` idx 6: necessary (total relation, LU vs LE0)
theorem inv6 : ¬ drop0% Cslib.LTS.IsBisimulation.inv 6 := fun H =>
  notBisEU _ (H (lts₁ := LU) (lts₂ := LE0) (r := fun _ _ => True)) trivial

-- `Cslib.LTS.Bisimilarity.symm` idx 7: necessary (LU vs LE0)
theorem bsymm7 : ¬ drop0% Cslib.LTS.Bisimilarity.symm 7 := fun H =>
  notBisimEU (H (lts₁ := LU) (lts₂ := LE0) (s₁ := ()) (s₂ := ()))

-- `Cslib.LTS.IsBisimulation.comp` idx 9: necessary (LU, LE0, LE0; total relations)
theorem comp9 : ¬ drop0% Cslib.LTS.IsBisimulation.comp 9 := fun H =>
  notBisUE _ (H (lts₁ := LU) (lts₂ := LE0) (lts₃ := LE0) (r1 := fun _ _ => True) (r2 := fun _ _ => True) e0Bis)
    ⟨(), trivial, trivial⟩

-- `Cslib.LTS.IsBisimulation.comp` idx 10: necessary (LE0, LE0, LU; total relations)
theorem comp10 : ¬ drop0% Cslib.LTS.IsBisimulation.comp 10 := fun H =>
  notBisEU _ (H (lts₁ := LE0) (lts₂ := LE0) (lts₃ := LU) (r1 := fun _ _ => True) (r2 := fun _ _ => True) e0Bis)
    ⟨(), trivial, trivial⟩

-- `Cslib.LTS.Bisimilarity.trans` idx 10: necessary (LU, LE0, LE0)
theorem btrans10 : ¬ drop0% Cslib.LTS.Bisimilarity.trans 10 := fun H =>
  notBisimUE (H (lts₁ := LU) (lts₂ := LE0) (lts₃ := LE0) (s₁ := ()) (s₂ := ()) (s₃ := ()) ⟨_, trivial, e0Bis⟩)

-- `Cslib.LTS.Bisimilarity.trans` idx 11: necessary (LE0, LE0, LU)
theorem btrans11 : ¬ drop0% Cslib.LTS.Bisimilarity.trans 11 := fun H =>
  notBisimEU (H (lts₁ := LE0) (lts₂ := LE0) (lts₃ := LU) (s₁ := ()) (s₂ := ()) (s₃ := ()) ⟨_, trivial, e0Bis⟩)

-- `Cslib.LTS.IsBisimulation.simulationEquiv` idx 8: necessary (total relation, LU vs LE0)
theorem simEq8 : ¬ drop0% Cslib.LTS.IsBisimulation.simulationEquiv 8 := fun H =>
  notSimUE (H (lts₁ := LU) (lts₂ := LE0) (r := fun _ _ => True) (s₁ := ()) (s₂ := ()) trivial).1

-- `Cslib.LTS.IsBisimulation.simulationEquiv` idx 9: necessary (empty bisimulation, LU vs LE0)
theorem simEq9 : ¬ drop0% Cslib.LTS.IsBisimulation.simulationEquiv 9 := fun H =>
  notSimUE (H (lts₁ := LU) (lts₂ := LE0) (r := fun _ _ => False) (s₁ := ()) (s₂ := ()) (botBis _ _)).1

-- `Cslib.LTS.IsBisimulation.sup` idx 7: necessary (r total, s empty, LU vs LE0)
theorem sup7 : ¬ drop0% Cslib.LTS.IsBisimulation.sup 7 := fun H =>
  notBisUE _ (H (lts₁ := LU) (lts₂ := LE0) (r := fun _ _ => True) (s := fun _ _ => False) (botBis _ _))
    (Or.inl trivial)

-- `Cslib.LTS.IsBisimulation.sup` idx 8: necessary (r empty, s total, LU vs LE0)
theorem sup8 : ¬ drop0% Cslib.LTS.IsBisimulation.sup 8 := fun H =>
  notBisUE _ (H (lts₁ := LU) (lts₂ := LE0) (r := fun _ _ => False) (s := fun _ _ => True) (botBis _ _))
    (Or.inr trivial)

-- `Cslib.LTS.IsBisimulation.le_bisimilarity` idx 6: necessary (total relation, LU vs LE0)
theorem leBis6 : ¬ drop0% Cslib.LTS.IsBisimulation.le_bisimilarity 6 := fun H =>
  notBisimUE (H (lts₁ := LU) (lts₂ := LE0) (r := fun _ _ => True) () () trivial)

-- `Cslib.LTS.Bisimilarity.gfp` idx 6: necessary (total relation, LU vs LE0)
theorem gfp6 : ¬ drop0% Cslib.LTS.Bisimilarity.gfp 6 := fun H => by
  have := congrFun (congrFun (H (lts₁ := LU) (lts₂ := LE0) (fun _ _ => True)) ()) ()
  apply notBisimUE
  rw [← this]
  exact Or.inr trivial

-- `Cslib.LTS.IsBisimulation.bisim_trace` idx 8: necessary (total relation, LU vs LE0)
theorem bt8 : ¬ drop0% Cslib.LTS.IsBisimulation.bisim_trace 8 := fun H => by
  obtain ⟨_, h, _⟩ := H (lts₁ := LU) (lts₂ := LE0) (r := fun _ _ => True) (s₁ := ()) (s₂ := ()) trivial [()] ()
    (.single _ trivial)
  cases h with | stepL h _ => exact h

-- `Cslib.LTS.IsBisimulation.bisim_trace` idx 9: necessary (empty bisimulation, LU vs LE0)
theorem bt9 : ¬ drop0% Cslib.LTS.IsBisimulation.bisim_trace 9 := fun H => by
  obtain ⟨_, h, _⟩ := H (lts₁ := LU) (lts₂ := LE0) (r := fun _ _ => False) (s₁ := ()) (s₂ := ()) (botBis _ _)
    [()] () (.single _ trivial)
  cases h with | stepL h _ => exact h

-- `Cslib.LTS.IsBisimulation.traceEq` idx 8: necessary (total relation, LU vs LE0)
theorem te8 : ¬ drop0% Cslib.LTS.IsBisimulation.traceEq 8 := fun H =>
  notTEUE (H (lts₁ := LU) (lts₂ := LE0) (r := fun _ _ => True) (s₁ := ()) (s₂ := ()) trivial)

-- `Cslib.LTS.IsBisimulation.traceEq` idx 9: necessary (empty bisimulation, LU vs LE0)
theorem te9 : ¬ drop0% Cslib.LTS.IsBisimulation.traceEq 9 := fun H =>
  notTEUE (H (lts₁ := LU) (lts₂ := LE0) (r := fun _ _ => False) (s₁ := ()) (s₂ := ()) (botBis _ _))

-- `Cslib.LTS.IsBisimulation.deterministic_traceEq_isBisimulation` idx 5: necessary (LD1 nondeterministic vs LD2)
theorem dtib5 : ¬ drop0% Cslib.LTS.IsBisimulation.deterministic_traceEq_isBisimulation 5 := fun H =>
  notBisD12 ⟨_, te12, H (lts₁ := LD1) (lts₂ := LD2)⟩

-- `Cslib.LTS.IsBisimulation.deterministic_traceEq_isBisimulation` idx 6: necessary (LD2 vs LD1 nondeterministic)
theorem dtib6 : ¬ drop0% Cslib.LTS.IsBisimulation.deterministic_traceEq_isBisimulation 6 := fun H =>
  notBisD21 ⟨_, te12.symm, H (lts₁ := LD2) (lts₂ := LD1)⟩

-- `Cslib.LTS.Bisimilarity.deterministic_traceEq_bisim` idx 7: necessary (LD1 nondeterministic vs LD2)
theorem dtb7 : ¬ drop0% Cslib.LTS.Bisimilarity.deterministic_traceEq_bisim 7 := fun H =>
  notBisD12 (H (s₁ := 0) (s₂ := 0) (lts₁ := LD1) (lts₂ := LD2) te12)

-- `Cslib.LTS.Bisimilarity.deterministic_traceEq_bisim` idx 8: necessary (LD2 vs LD1 nondeterministic)
theorem dtb8 : ¬ drop0% Cslib.LTS.Bisimilarity.deterministic_traceEq_bisim 8 := fun H =>
  notBisD21 (H (s₁ := 0) (s₂ := 0) (lts₁ := LD2) (lts₂ := LD1) te12.symm)

-- `Cslib.LTS.Bisimilarity.deterministic_traceEq_bisim` idx 9: necessary (edge false → true; false, true)
theorem dtb9 : ¬ drop0% Cslib.LTS.Bisimilarity.deterministic_traceEq_bisim 9 := fun H =>
  notBisLB (H (s₁ := false) (s₂ := true) (lts₁ := LB) (lts₂ := LB))

-- `Cslib.LTS.Deterministic.bisim_tfae` idx 5: necessary (LD1 nondeterministic vs LD2)
theorem tfae5 : ¬ drop0% Cslib.LTS.Deterministic.bisim_tfae 5 := fun H =>
  notBisD12 (((H (lts₁ := LD1) (lts₂ := LD2) 0 0).out 2 1).1 te12)

-- `Cslib.LTS.Deterministic.bisim_tfae` idx 6: necessary (LD2 vs LD1 nondeterministic)
theorem tfae6 : ¬ drop0% Cslib.LTS.Deterministic.bisim_tfae 6 := fun H =>
  notBisD21 (((H (lts₁ := LD2) (lts₂ := LD1) 0 0).out 2 1).1 te12.symm)

-- `Cslib.LTS.Bisimilarity.deterministic_bisim_eq_traceEq` idx 5: necessary (LD1 nondeterministic vs LD2)
theorem dbe5 : ¬ drop0% Cslib.LTS.Bisimilarity.deterministic_bisim_eq_traceEq 5 := fun H => by
  have := congrFun (congrFun (H (lts₁ := LD1) (lts₂ := LD2)) 0) 0
  apply notBisD12
  rw [this]
  exact te12

-- `Cslib.LTS.Bisimilarity.deterministic_bisim_eq_traceEq` idx 6: necessary (LD2 vs LD1 nondeterministic)
theorem dbe6 : ¬ drop0% Cslib.LTS.Bisimilarity.deterministic_bisim_eq_traceEq 6 := fun H => by
  have := congrFun (congrFun (H (lts₁ := LD2) (lts₂ := LD1)) 0) 0
  apply notBisD21
  rw [this]
  exact te12.symm


-- ===== weak bisimulation (τ = false on Bool labels) =====

@[reducible] def tauB : HasTau Bool := ⟨false⟩
attribute [local instance] tauB
def LUB : LTS Unit Bool := ⟨fun _ _ _ => True⟩
def LUB0 : LTS Unit Bool := ⟨fun _ _ _ => False⟩

theorem noSTr {s t : Unit} {μ : Bool} (h : LUB0.STr s μ t) : μ = false := by
  cases h with
  | refl => rfl
  | tr _ h _ => exact h.elim
theorem wb00 : LTS.IsWeakBisimulation LUB0 LUB0 (fun _ _ => True) :=
  fun _ _ _ _ => ⟨fun s' h => ⟨s', h, trivial⟩, fun s' h => ⟨s', h, trivial⟩⟩
theorem sw00 : LTS.IsSWBisimulation LUB0 LUB0 (fun _ _ => True) :=
  fun _ _ _ _ => ⟨fun _ h => h.elim, fun _ h => h.elim⟩
theorem notWBUE (r : Unit → Unit → Prop) (hb : LTS.IsWeakBisimulation LUB LUB0 r)
    (hr : r () ()) : False := by
  obtain ⟨_, h, _⟩ := (hb hr true).1 () (LTS.STr.single (lts := LUB) (s := ()) (μ := true) (s' := ()) trivial)
  exact absurd (noSTr h) (by decide)
theorem notWBEU (r : Unit → Unit → Prop) (hb : LTS.IsWeakBisimulation LUB0 LUB r)
    (hr : r () ()) : False := by
  obtain ⟨_, h, _⟩ := (hb hr true).2 () (LTS.STr.single (lts := LUB) (s := ()) (μ := true) (s' := ()) trivial)
  exact absurd (noSTr h) (by decide)
theorem notSWUE (r : Unit → Unit → Prop) (hb : LTS.IsSWBisimulation LUB LUB0 r)
    (hr : r () ()) : False := by
  obtain ⟨_, h, _⟩ := (hb hr true).1 () trivial
  exact absurd (noSTr h) (by decide)
theorem notSWEU (r : Unit → Unit → Prop) (hb : LTS.IsSWBisimulation LUB0 LUB r)
    (hr : r () ()) : False := by
  obtain ⟨_, h, _⟩ := (hb hr true).2 () trivial
  exact absurd (noSTr h) (by decide)

-- `Cslib.LTS.IsSWBisimulation.isSimulation` idx 7: necessary (total relation; LUB steps with true, LUB0 empty)
theorem swSim7 : ¬ drop0% Cslib.LTS.IsSWBisimulation.isSimulation 7 := fun H => by
  obtain ⟨_, h, _⟩ := H (lts₁ := LUB) (lts₂ := LUB0) (r := fun _ _ => True)
    (s₁ := ()) (s₂ := ()) trivial true () trivial
  exact absurd (noSTr h) (by decide)

-- `Cslib.LTS.IsSWBisimulation.isSimulation_flip` idx 7: necessary (total relation; LUB0 vs LUB)
theorem swSimF7 : ¬ drop0% Cslib.LTS.IsSWBisimulation.isSimulation_flip 7 := fun H => by
  obtain ⟨_, h, _⟩ := H (lts₁ := LUB0) (lts₂ := LUB) (r := fun _ _ => True)
    (s₁ := ()) (s₂ := ()) trivial true () trivial
  exact absurd (noSTr h) (by decide)

-- `Cslib.LTS.IsWeakBisimulation.isSwBisimulation` idx 7: necessary (total relation; LUB vs LUB0)
theorem wbSw7 : ¬ drop0% Cslib.LTS.IsWeakBisimulation.isSwBisimulation 7 := fun H =>
  notSWUE _ (H (lts₁ := LUB) (lts₂ := LUB0) (r := fun _ _ => True)) trivial

-- `Cslib.LTS.IsSWBisimulation.isWeakBisimulation` idx 7: necessary (total relation; LUB vs LUB0)
theorem swWb7 : ¬ drop0% Cslib.LTS.IsSWBisimulation.isWeakBisimulation 7 := fun H =>
  notWBUE _ (H (lts₁ := LUB) (lts₂ := LUB0) (r := fun _ _ => True)) trivial

-- `Cslib.LTS.IsWeakBisimulation.inv` idx 7: necessary (total relation; LUB0 vs LUB)
theorem wbInv7 : ¬ drop0% Cslib.LTS.IsWeakBisimulation.inv 7 := fun H =>
  notWBUE _ (H (lts₁ := LUB0) (lts₂ := LUB) (fun _ _ => True)) trivial

-- `Cslib.LTS.WeakBisimilarity.symm` idx 8: necessary (LUB0 vs LUB)
theorem wbSymm8 : ¬ drop0% Cslib.LTS.WeakBisimilarity.symm 8 := fun H => by
  obtain ⟨r, hr, hb⟩ := H (lts₁ := LUB0) (lts₂ := LUB) (s₁ := ()) (s₂ := ())
  exact notWBUE r hb hr

-- `Cslib.LTS.IsWeakBisimulation.comp` idx 10: necessary (LUB, LUB0, LUB0; total relations)
theorem wbComp10 : ¬ drop0% Cslib.LTS.IsWeakBisimulation.comp 10 := fun H =>
  notWBUE _ (H (lts₁ := LUB) (lts₂ := LUB0) (lts₃ := LUB0) (r1 := fun _ _ => True)
    (r2 := fun _ _ => True) wb00) ⟨(), trivial, trivial⟩

-- `Cslib.LTS.IsWeakBisimulation.comp` idx 11: necessary (LUB0, LUB0, LUB; total relations)
theorem wbComp11 : ¬ drop0% Cslib.LTS.IsWeakBisimulation.comp 11 := fun H =>
  notWBEU _ (H (lts₁ := LUB0) (lts₂ := LUB0) (lts₃ := LUB) (r1 := fun _ _ => True)
    (r2 := fun _ _ => True) wb00) ⟨(), trivial, trivial⟩

-- `Cslib.LTS.IsSWBisimulation.comp` idx 10: necessary (LUB, LUB0, LUB0; total relations)
theorem swComp10 : ¬ drop0% Cslib.LTS.IsSWBisimulation.comp 10 := fun H =>
  notSWUE _ (H (lts₁ := LUB) (lts₂ := LUB0) (lts₃ := LUB0) (r1 := fun _ _ => True)
    (r2 := fun _ _ => True) sw00) ⟨(), trivial, trivial⟩

-- `Cslib.LTS.IsSWBisimulation.comp` idx 11: necessary (LUB0, LUB0, LUB; total relations)
theorem swComp11 : ¬ drop0% Cslib.LTS.IsSWBisimulation.comp 11 := fun H =>
  notSWEU _ (H (lts₁ := LUB0) (lts₂ := LUB0) (lts₃ := LUB) (r1 := fun _ _ => True)
    (r2 := fun _ _ => True) sw00) ⟨(), trivial, trivial⟩

-- `Cslib.LTS.WeakBisimilarity.trans` idx 11: necessary (LUB, LUB0, LUB0)
theorem wbTrans11 : ¬ drop0% Cslib.LTS.WeakBisimilarity.trans 11 := fun H => by
  obtain ⟨r, hr, hb⟩ := H (lts₁ := LUB) (lts₂ := LUB0) (lts₃ := LUB0) (s₁ := ()) (s₂ := ())
    (s₃ := ()) ⟨_, trivial, wb00⟩
  exact notWBUE r hb hr

-- `Cslib.LTS.WeakBisimilarity.trans` idx 12: necessary (LUB0, LUB0, LUB)
theorem wbTrans12 : ¬ drop0% Cslib.LTS.WeakBisimilarity.trans 12 := fun H => by
  obtain ⟨r, hr, hb⟩ := H (lts₁ := LUB0) (lts₂ := LUB0) (lts₃ := LUB) (s₁ := ()) (s₂ := ())
    (s₃ := ()) ⟨_, trivial, wb00⟩
  exact notWBEU r hb hr

-- ===== LTS.Divergence =====

-- `Cslib.LTS.divergentTrace_drop` idx 3: necessary (τ = false, μs constantly true)
theorem divDrop3 : ¬ drop0% Cslib.LTS.divergentTrace_drop 3 := fun H =>
  absurd (H (μs := ⟨fun _ => true⟩) 0 0) (by decide)

-- `Cslib.LTS.DivergenceFree.divergence_free` idx 4: necessary (one state with a τ-loop)
theorem divFree4 : ¬ drop0% Cslib.LTS.DivergenceFree.divergence_free 4 := fun H =>
  @H Bool Unit tauB LUB ⟨(), ⟨fun _ => ()⟩, ⟨fun _ => false⟩, fun _ => trivial, rfl, fun _ => rfl⟩

-- ===== LTS.Execution =====

-- `Cslib.LTS.Execution.of_tr` idx 6: necessary (empty LTS on ℕ)
theorem exOfTr6 : ¬ drop0% Cslib.LTS.Execution.of_tr 6 := fun H =>
  (H (lts := LN0) (s := 0) (μ := ()) (t := 0)).trans 0 (by simp)

-- `Cslib.LTS.Execution.mk` idx 8: necessary (s = 1, ss = [0], μs = [])
theorem exMk8 : ¬ drop0% Cslib.LTS.Execution.mk 8 := fun H => by
  have := (H (lts := LN0) (s := 1) (t := 0) (μs := []) (ss := [0]) rfl rfl (fun k hk => absurd hk (by simp))).start
  simp at this

-- `Cslib.LTS.Execution.mk` idx 9: necessary (t = 1, ss = [0], μs = [])
theorem exMk9 : ¬ drop0% Cslib.LTS.Execution.mk 9 := fun H => by
  have := (H (lts := LN0) (s := 0) (t := 1) (μs := []) (ss := [0]) rfl rfl (fun k hk => absurd hk (by simp))).last
  simp at this

-- `Cslib.LTS.Execution.mk` idx 10: necessary (empty LTS, ss = [0, 0], μs = [()])
theorem exMk10 : ¬ drop0% Cslib.LTS.Execution.mk 10 := fun H =>
  (H (lts := LN0) (s := 0) (t := 0) (μs := [()]) (ss := [0, 0]) rfl rfl rfl).trans 0 (by simp)

-- `Cslib.LTS.Execution.isChain` idx 7: necessary (empty LTS, ss = [0, 0])
theorem exChain7 : ¬ drop0% Cslib.LTS.Execution.isChain 7 := fun H => by
  have := H (lts := LN0) (s := 0) (μs := []) (t := 0) (ss := [0, 0])
  simp [LTS.UnlabelledTr, LN0] at this

-- `Cslib.LTS.Execution.take` idx 7: necessary (s = 1, ss = [0], n = 0)
theorem exTake7 : ¬ drop0% Cslib.LTS.Execution.take 7 := fun H => by
  have := (H (lts := LN0) (s := 1) (μs := []) (t := 0) (ss := [0]) 0 (by simp)).start
  simp at this

-- `Cslib.LTS.Execution.drop` idx 7: necessary (t = 1, ss = [0], n = 0)
theorem exDrop7 : ¬ drop0% Cslib.LTS.Execution.drop 7 := fun H => by
  have := (H (lts := LN0) (s := 0) (μs := []) (t := 1) (ss := [0]) 0 (by simp)).last
  simp at this

end W1c3

namespace W1c3
open Cslib

-- ===== Frame =====

abbrev τU : PFunctor := PFunctor.mkUnary Unit
abbrev τB : PFunctor := PFunctor.mkUnary Bool

def F0 : Frame Unit τU := ⟨fun _ _ _ => False⟩
def FB : Frame Unit τB := ⟨fun op _ _ => op = true⟩
def F1 : Frame Bool τU := ⟨fun _ w ws => w = false ∧ ws () = true⟩
def FS : Frame ℕ τU := ⟨fun _ w ws => ws () = w + 1⟩
def FT : Frame Bool τU := ⟨fun _ _ ws => ws () = true⟩
def FF : Frame Bool τU := ⟨fun _ w ws => w = false ∧ ws () = false⟩

theorem F1trans : F1.Trans () := ⟨fun _ _ _ _ h1 h2 => absurd (h1.2.symm.trans h2.1) (by decide)⟩

-- `Cslib.Frame.r_const_of_diagonal` idx 6: necessary (empty frame)
theorem rcd6 : ¬ drop0% Cslib.Frame.r_const_of_diagonal 6 := fun H =>
  H (World := Unit) (τ := τU) (op := ()) (w := ()) (w' := ()) (f := F0)

-- `Cslib.Frame.diagonal_of_r` idx 7: necessary (empty frame)
theorem dor7 : ¬ drop0% Cslib.Frame.diagonal_of_r 7 := fun H =>
  H (World := Unit) (τ := τU) (op := ()) (w := ()) (ws := fun _ => ()) (f := F0)

-- `Cslib.Frame.DiagonalInverse.diagonalInverse` idx 5: necessary (op true total, op false empty)
theorem diagInv5 : ¬ drop0% Cslib.Frame.DiagonalInverse.diagonalInverse 5 := fun H =>
  absurd ((H (f := FB) (op₁ := true) (op₂ := false) () ()).1 rfl) (by simp [FB, Frame.diagonal])

-- `Cslib.Frame.instDiagonalInverse` idx 5: necessary (op true total, op false empty)
theorem instDI5 : ¬ drop0% Cslib.Frame.instDiagonalInverse 5 := fun H =>
  absurd (((H FB true false).diagonalInverse () ()).2 rfl) (by simp [FB, Frame.diagonal])

-- `Cslib.Frame.DiagonalSymm.symm` idx 4: necessary (single edge false → true)
theorem dsym4 : ¬ drop0% Cslib.Frame.DiagonalSymm.symm 4 := fun H => by
  obtain ⟨_, h⟩ := H (f := F1) (op := ()) false (fun _ => true) ⟨rfl, rfl⟩
  exact absurd h.1 (by decide)

-- `Cslib.Frame.DiagonalSymm.symm` idx 7: necessary (empty frame)
theorem dsym7 : ¬ drop0% Cslib.Frame.DiagonalSymm.symm 7 := fun H => by
  obtain ⟨_, h⟩ := H (f := F0) (op := ()) (self := ⟨fun _ _ h => h.elim⟩) () (fun _ => ())
  exact h

-- `Cslib.Frame.Trans.trans` idx 4: necessary (successor frame on ℕ)
theorem trans4 : ¬ drop0% Cslib.Frame.Trans.trans 4 := fun H => by
  have h := H (f := FS) (op := ()) 0 (fun _ => 1) () (fun _ => 2) rfl rfl
  exact absurd h (by simp [FS])

-- `Cslib.Frame.Trans.trans` idx 9: necessary (single edge false → true, w = true)
theorem trans9 : ¬ drop0% Cslib.Frame.Trans.trans 9 := fun H =>
  absurd (H (f := F1) (op := ()) (self := F1trans) true (fun _ => false) () (fun _ => true) ⟨rfl, rfl⟩).1
    (by decide)

-- `Cslib.Frame.Trans.trans` idx 10: necessary (single edge false → true, ws₂ = false)
theorem trans10 : ¬ drop0% Cslib.Frame.Trans.trans 10 := fun H =>
  absurd (H (f := F1) (op := ()) (self := F1trans) false (fun _ => true) () (fun _ => false) ⟨rfl, rfl⟩).2
    (by decide)

-- `Cslib.Frame.instIsTransProjectOfTrans` idx 4: necessary (successor frame on ℕ)
theorem isTransProj4 : ¬ drop0% Cslib.Frame.instIsTransProjectOfTrans 4 := fun H => by
  obtain ⟨ws, h1, h2⟩ := @IsTrans.trans _ _ (H (f := FS) (op := ()) ()) 0 1 2 ⟨fun _ => 1, rfl, rfl⟩
    ⟨fun _ => 2, rfl, rfl⟩
  simp only [FS] at h1
  omega

-- `Cslib.Frame.RightEuclidean.rightEuclidean` idx 4: necessary (single edge false → true)
theorem re4 : ¬ drop0% Cslib.Frame.RightEuclidean.rightEuclidean 4 := fun H => by
  obtain ⟨_, h⟩ := H (f := F1) (op := ()) false (fun _ => true) (fun _ => true) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
  exact absurd h.1 (by decide)

-- `Cslib.Frame.RightEuclidean.rightEuclidean` idx 8: necessary (every world sees true; ws₁ = false)
theorem re8 : ¬ drop0% Cslib.Frame.RightEuclidean.rightEuclidean 8 := fun H => by
  obtain ⟨_, h⟩ := H (f := FT) (op := ()) (self := ⟨fun _ _ _ h1 _ => ⟨(), h1⟩⟩) true (fun _ => false)
    (fun _ => true) rfl
  simp [FT] at h

-- `Cslib.Frame.RightEuclidean.rightEuclidean` idx 9: necessary (false sees false only; ws₂ = true)
theorem re9 : ¬ drop0% Cslib.Frame.RightEuclidean.rightEuclidean 9 := fun H => by
  obtain ⟨_, h⟩ := H (f := FF) (op := ()) (self := ⟨fun _ _ _ h1 h2 => ⟨(), h2.2, h1.2⟩⟩) false
    (fun _ => false) (fun _ => true) ⟨rfl, rfl⟩
  exact absurd h.1 (by decide)

-- ===== RelationAlgebra =====

/-- Every Boolean algebra is a relation algebra with composition `⊓`, identity `⊤`, converse `id`. -/
def BA (β : Type) := β
instance BA.ba (β : Type) [h : BooleanAlgebra β] : BooleanAlgebra (BA β) := h
instance BA.inst (β : Type) [BooleanAlgebra β] : RelationAlgebra (BA β) where
  mul a b := a ⊓ b
  one := ⊤
  mul_assoc := inf_assoc
  one_mul := top_inf_eq
  mul_one := inf_top_eq
  star := id
  star_involutive := fun _ => rfl
  star_mul := inf_comm
  sup_mul := inf_sup_right
  star_sup := fun _ _ => rfl
  tarski := fun a b => by
    show a ⊓ (a ⊓ b)ᶜ ≤ bᶜ
    rw [compl_inf, inf_sup_left, inf_compl_self, bot_sup_eq]
    exact inf_le_right
instance : IsAtomic (BA (Set Bool)) := inferInstanceAs (IsAtomic (Set Bool))

abbrev SB := BA (Set Bool)
theorem atT : IsAtom (({true} : Set Bool) : SB) := Set.isAtom_singleton true

-- `Cslib.RelationAlgebra.atom_cycle_left` idx 5: necessary (Set Bool with ⊓; r = s = ⊤, p = {true})
theorem acl5 : ¬ drop0% Cslib.RelationAlgebra.atom_cycle_left 5 := fun H => by
  have := H (α := SB) (r := ⊤) (s := ⊤) (p := ({true} : Set Bool))
    (Set.singleton_ne_empty true) (fun _ _ => ⟨trivial, trivial⟩)
  have h2 := (this (show false ∈ (Set.univ : Set Bool) from trivial)).2
  simp at h2

-- `Cslib.RelationAlgebra.atom_cycle_left` idx 6: necessary (Set Bool with ⊓; p = ⊥)
theorem acl6 : ¬ drop0% Cslib.RelationAlgebra.atom_cycle_left 6 := fun H =>
  (H (α := SB) (r := ⊤) (s := ({true} : Set Bool)) (p := ⊥) atT bot_le (show true ∈ ({true} : Set Bool) from rfl)).2

-- `Cslib.RelationAlgebra.atom_cycle_left` idx 7: necessary (Set Bool with ⊓; r = ⊥)
theorem acl7 : ¬ drop0% Cslib.RelationAlgebra.atom_cycle_left 7 := fun H =>
  (H (α := SB) (r := ⊥) (s := ({true} : Set Bool)) (p := ({true} : Set Bool)) atT (Set.singleton_ne_empty true)
    (show true ∈ ({true} : Set Bool) from rfl)).1

-- `Cslib.RelationAlgebra.exists_atom_le_mul_right` idx 6: necessary (p = b = ⊥)
theorem ealr6 : ¬ drop0% Cslib.RelationAlgebra.exists_atom_le_mul_right 6 := fun H => by
  obtain ⟨s, hs, hsb, _⟩ := H (α := SB) (a := ⊤) (b := ⊥) (p := ⊥) bot_le
  exact hs.ne_bot (le_bot_iff.mp hsb)

-- `Cslib.RelationAlgebra.exists_atom_le_mul_right` idx 7: necessary (b = ⊥)
theorem ealr7 : ¬ drop0% Cslib.RelationAlgebra.exists_atom_le_mul_right 7 := fun H => by
  obtain ⟨s, hs, hsb, _⟩ := H (α := SB) (a := ⊤) (b := ⊥) (p := ({true} : Set Bool)) atT
  exact hs.ne_bot (le_bot_iff.mp hsb)

-- `Cslib.RelationAlgebra.exists_atom_le_mul_left` idx 6: necessary (p = a = ⊥)
theorem eall6 : ¬ drop0% Cslib.RelationAlgebra.exists_atom_le_mul_left 6 := fun H => by
  obtain ⟨s, hs, hsb, _⟩ := H (α := SB) (a := ⊥) (b := ⊤) (p := ⊥) bot_le
  exact hs.ne_bot (le_bot_iff.mp hsb)

-- `Cslib.RelationAlgebra.exists_atom_le_mul_left` idx 7: necessary (a = ⊥)
theorem eall7 : ¬ drop0% Cslib.RelationAlgebra.exists_atom_le_mul_left 7 := fun H => by
  obtain ⟨s, hs, hsb, _⟩ := H (α := SB) (a := ⊥) (b := ⊤) (p := ({true} : Set Bool)) atT
  exact hs.ne_bot (le_bot_iff.mp hsb)

-- `Cslib.RelationAlgebra.le_compl_one_of_mem_nonsymmetricDiversityAtoms` idx 3: necessary (a = 1 = ⊤)
theorem lco3 : ¬ drop0% Cslib.RelationAlgebra.le_compl_one_of_mem_nonsymmetricDiversityAtoms 3 := fun H =>
  (H (α := SB) (a := 1)) (show true ∈ (Set.univ : Set Bool) from trivial) trivial

-- coordinate swap on `Bool → BA Bool`
abbrev P2 := Bool → BA Bool
def swapH : RelationAlgebraHom P2 P2 where
  toFun x i := x (!i)
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl
  map_top' := rfl
  map_bot' := rfl
  map_one' := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

def swapE : RelationAlgebraEquiv P2 P2 where
  toFun x i := x (!i)
  invFun x i := x (!i)
  left_inv x := funext fun i => by simp
  right_inv x := funext fun i => by simp
  map_rel_iff' := ⟨fun h i => by have := h (!i); simpa using this, fun h i => h _⟩
  map_mul' _ _ := rfl
  map_star' _ := rfl

-- `Cslib.RelationAlgebraHom.ext` idx 6: necessary (coordinate swap ≠ identity)
theorem homExt6 : ¬ drop0% Cslib.RelationAlgebraHom.ext 6 := fun H => by
  have := congrArg (fun f : RelationAlgebraHom P2 P2 => f (fun i => i) true)
    (H (f := swapH) (g := RelationAlgebraHom.id _))
  change (false : Bool) = true at this
  exact absurd this (by decide)

-- `Cslib.RelationAlgebraEquiv.ext` idx 6: necessary (coordinate swap ≠ identity)
theorem equivExt6 : ¬ drop0% Cslib.RelationAlgebraEquiv.ext 6 := fun H => by
  have := congrArg (fun f : RelationAlgebraEquiv P2 P2 => f (fun i => i) true)
    (H (f := swapE) (g := RelationAlgebraEquiv.refl _))
  change (false : Bool) = true at this
  exact absurd this (by decide)

end W1c3
