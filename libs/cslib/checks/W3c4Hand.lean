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

namespace W3c4
open Cslib Cslib.LTS

@[reducible] def tauB : HasTau Bool := ⟨false⟩
attribute [local instance] tauB

-- empty LTS on Bool states, Bool labels
def E2 : LTS Bool Bool := ⟨fun _ _ _ => False⟩
-- one τ-step false → true
def T2 : LTS Bool Bool := ⟨fun s _ t => s = false ∧ t = true⟩
def LUB0 : LTS Unit Bool := ⟨fun _ _ _ => False⟩
def LN0 : LTS ℕ Unit := ⟨fun _ _ _ => False⟩
def LSU : LTS ℕ Unit := ⟨fun s _ t => t = s + 1⟩

theorem e2STr {s t : Bool} {μ : Bool} (h : E2.STr s μ t) : s = t := by
  cases h with
  | refl => rfl
  | tr _ h _ => exact h.elim
theorem e2SMTr {s t : Bool} (h : E2.SMTr s [] t) : s = t := by
  cases h with
  | τ h => exact e2STr h
theorem ln0MTr {s t : ℕ} {l : List Unit} (h : LN0.MTr s l t) : l = [] := by
  cases h with
  | refl => rfl
  | stepL h _ => exact h.elim

-- `Cslib.LTS.STr.single` idx 7: necessary (empty LTS, label true ≠ τ)
theorem stSingle7 : ¬ drop0% Cslib.LTS.STr.single 7 := fun H => by
  have := @H Bool Bool false false true tauB E2
  cases this with
  | tr _ h _ => exact h.elim

-- `Cslib.LTS.STr.trans_τ` idx 7: necessary (empty LTS, s1 = false, s2 = s3 = true)
theorem stTrans7 : ¬ drop0% Cslib.LTS.STr.trans_τ 7 := fun H =>
  absurd (e2STr (H (lts := E2) (s1 := false) (s2 := true) (s3 := true) .refl)) (by decide)

-- `Cslib.LTS.STr.trans_τ` idx 8: necessary (empty LTS, s1 = s2 = false, s3 = true)
theorem stTrans8 : ¬ drop0% Cslib.LTS.STr.trans_τ 8 := fun H =>
  absurd (e2STr (H (lts := E2) (s1 := false) (s2 := false) (s3 := true) .refl)) (by decide)

-- `Cslib.LTS.STr.comp` idx 9: necessary (empty LTS, s1 = false, others true, μ = τ)
theorem stComp9 : ¬ drop0% Cslib.LTS.STr.comp 9 := fun H =>
  absurd (e2STr (H (lts := E2) (s1 := false) (s2 := true) (s3 := true) (s4 := true) (μ := false)
    .refl .refl)) (by decide)

-- `Cslib.LTS.STr.comp` idx 10: necessary (empty LTS, s1 = s2 = false, s3 = s4 = true, μ = τ)
theorem stComp10 : ¬ drop0% Cslib.LTS.STr.comp 10 := fun H =>
  absurd (e2STr (H (lts := E2) (s1 := false) (s2 := false) (s3 := true) (s4 := true) (μ := false)
    .refl .refl)) (by decide)

-- `Cslib.LTS.STr.comp` idx 11: necessary (empty LTS, s1 = s2 = s3 = false, s4 = true, μ = τ)
theorem stComp11 : ¬ drop0% Cslib.LTS.STr.comp 11 := fun H =>
  absurd (e2STr (H (lts := E2) (s1 := false) (s2 := false) (s3 := false) (s4 := true) (μ := false)
    .refl .refl)) (by decide)

-- `Cslib.LTS.τClosure_mono` idx 6: necessary (S = univ, T = ∅)
theorem tcMono6 : ¬ drop0% Cslib.LTS.τClosure_mono 6 := fun H => by
  have h1 : () ∈ LUB0.τClosure Set.univ := LTS.τClosure_subset LUB0 trivial
  have := H LUB0 (S := Set.univ) (T := ∅) h1
  simp at this

-- `Cslib.LTS.saturate_setImage_of_ne_τ` idx 6: necessary (μ = τ, empty LTS, S = univ)
theorem satSetImage6 : ¬ drop0% Cslib.LTS.saturate_setImage_of_ne_τ 6 := fun H => by
  have h1 : () ∈ LUB0.saturate.setImage Set.univ false := (LTS.subset_saturate_setImage_τ LUB0) trivial
  rw [H LUB0 (S := Set.univ) (μ := false), LTS.mem_τClosure_iff] at h1
  obtain ⟨s, hs, _⟩ := h1
  rw [LTS.mem_setImage] at hs
  obtain ⟨_, _, h⟩ := hs
  exact h

-- `Cslib.LTS.SMTr.comp` idx 9: necessary (empty LTS, empty label lists, s₁ = false, s₂ = s₃ = true)
theorem smComp9 : ¬ drop0% Cslib.LTS.SMTr.comp 9 := fun H =>
  absurd (e2SMTr (H (lts := E2) (s₁ := false) (s₂ := true) (s₃ := true) (μs₁ := []) (μs₂ := [])
    (LTS.SMTr.refl _ _))) (by decide)

-- `Cslib.LTS.SMTr.comp` idx 10: necessary (empty LTS, empty label lists, s₁ = s₂ = false, s₃ = true)
theorem smComp10 : ¬ drop0% Cslib.LTS.SMTr.comp 10 := fun H =>
  absurd (e2SMTr (H (lts := E2) (s₁ := false) (s₂ := false) (s₃ := true) (μs₁ := []) (μs₂ := [])
    (LTS.SMTr.refl _ _))) (by decide)

-- `Cslib.LTS.SMTr.fromMTr` idx 7: necessary (empty LTS, s = false, s' = true, μs = [])
theorem smFrom7 : ¬ drop0% Cslib.LTS.SMTr.fromMTr 7 := fun H =>
  absurd (e2SMTr (H (lts := E2) (s := false) (s' := true) (μs := []))) (by decide)

-- `Cslib.LTS.saturate_mTr_sMTr_not_nil_iff` idx 7: necessary (μs = [], one τ-step false → true)
theorem satNN7 : ¬ drop0% Cslib.LTS.saturate_mTr_sMTr_not_nil_iff 7 := fun H => by
  have h : T2.SMTr false [] true := .τ (LTS.STr.single (lts := T2) (μ := false) ⟨rfl, rfl⟩)
  rw [← H (lts := T2)] at h
  exact absurd h.nil_eq (by decide)

-- `Cslib.LTS.sMTr_iff_exists_mTr_filter` idx 8: necessary (μs = [τ]: filtered lists never contain τ)
theorem smFilter8 : ¬ drop0% Cslib.LTS.sMTr_iff_exists_mTr_filter 8 := fun H => by
  have h : E2.SMTr false [false] false := .stepL .refl (LTS.SMTr.refl _ _)
  rw [H (lts := E2)] at h
  obtain ⟨νs, hν, _⟩ := h
  have : false ∈ νs.filter (· ≠ HasTau.τ) := by rw [hν]; simp
  simp at this

-- `Cslib.LTS.Morphism.labelMap_tr` idx 6: necessary (empty source LTS, labels mapped to idle)
theorem lmTr6 : ¬ drop0% Cslib.LTS.Morphism.labelMap_tr 6 := fun H => by
  have := H (lts₁ := ⟨Bool, Unit, ⟨fun _ _ _ => False⟩⟩) (lts₂ := ⟨Bool, Unit, ⟨fun _ _ _ => False⟩⟩)
    ⟨id, fun _ => none, fun _ _ _ h => h.elim⟩ false true ()
  simp [LTS.withIdle] at this

-- `Cslib.LTS.OmegaExecution.extract_execution` idx 5: necessary (empty LTS, n = 0, m = 1)
theorem oeExtE5 : ¬ drop0% Cslib.LTS.OmegaExecution.extract_execution 5 := fun H => by
  have := congrArg List.length (ln0MTr (H (lts := LN0) (ss := ⟨fun n => n⟩) (μs := ⟨fun _ => ()⟩)
    (n := 0) (m := 1) (by omega)).to_mTr)
  simp [ωSequence.length_extract] at this

-- `Cslib.LTS.OmegaExecution.extract_execution` idx 8: necessary (successor LTS, n = 1, m = 0)
theorem oeExtE8 : ¬ drop0% Cslib.LTS.OmegaExecution.extract_execution 8 := fun H => by
  have h := (H (lts := LSU) (ss := ⟨fun n => n⟩) (μs := ⟨fun _ => ()⟩) (fun _ => rfl)
    (n := 1) (m := 0)).to_mTr
  have hl : (ωSequence.mk (fun _ => ())).extract 1 0 = [] :=
    List.eq_nil_of_length_eq_zero (by simp [ωSequence.length_extract])
  rw [hl] at h
  exact absurd h.nil_eq (by simp)

-- `Cslib.LTS.OmegaExecution.extract_mTr` idx 5: necessary (empty LTS, n = 0, m = 1)
theorem oeExtM5 : ¬ drop0% Cslib.LTS.OmegaExecution.extract_mTr 5 := fun H => by
  have := congrArg List.length (ln0MTr (H (lts := LN0) (ss := ⟨fun n => n⟩) (μs := ⟨fun _ => ()⟩)
    (n := 0) (m := 1) (by omega)))
  simp [ωSequence.length_extract] at this

-- `Cslib.LTS.OmegaExecution.extract_mTr` idx 8: necessary (successor LTS, n = 1, m = 0)
theorem oeExtM8 : ¬ drop0% Cslib.LTS.OmegaExecution.extract_mTr 8 := fun H => by
  have h := H (lts := LSU) (ss := ⟨fun n => n⟩) (μs := ⟨fun _ => ()⟩) (fun _ => rfl)
    (n := 1) (m := 0)
  have hl : (ωSequence.mk (fun _ => ())).extract 1 0 = [] :=
    List.eq_nil_of_length_eq_zero (by simp [ωSequence.length_extract])
  rw [hl] at h
  exact absurd h.nil_eq (by simp)

end W3c4

namespace W3c4
open Cslib Cslib.LTS

attribute [local instance] tauB
def LU : LTS Unit Unit := ⟨fun _ _ _ => True⟩
def LE0 : LTS Unit Unit := ⟨fun _ _ _ => False⟩
def LB : LTS Bool Unit := ⟨fun s _ t => s = false ∧ t = true⟩

theorem lsuOE (f : ℕ → ℕ) (hf : ∀ n, f (n + 1) = f n + 1) (μs : ωSequence Unit) :
    LSU.OmegaExecution ⟨f⟩ μs := fun i => hf i
theorem ln0OE {ss : ωSequence ℕ} {μs : ωSequence Unit} (h : LN0.OmegaExecution ss μs) : False := h 0
theorem e2τ {s t : Bool} (h : E2.τSTr s t) : s = t := by
  rcases h.cases_tail with h | ⟨_, _, h⟩
  · exact h.symm
  · exact h.elim
theorem notSimUE : ¬ LU.IsSimulation LE0 (fun _ _ => True) := fun h => by
  obtain ⟨_, h, _⟩ := h (s₁ := ()) (s₂ := ()) trivial () () trivial; exact h
theorem simUU : LU.IsSimulation LU (fun _ _ => True) := fun _ _ _ _ _ _ => ⟨(), trivial, trivial⟩
theorem simEE : LE0.IsSimulation LE0 (fun _ _ => True) := fun _ _ _ _ _ h => h.elim
theorem notSimilarUE : ¬ LU.Similarity LE0 () () := fun ⟨r, hr, hs⟩ => by
  obtain ⟨_, h, _⟩ := hs hr () () trivial; exact h

-- `Cslib.LTS.OmegaExecution.cons` idx 8: necessary (successor LTS, s = 5, t = 1, ss n = n + 1)
theorem oeCons8 : ¬ drop0% Cslib.LTS.OmegaExecution.cons 8 := fun H => by
  have := H (lts := LSU) (s := 5) (t := 1) (μ := ()) (ss := ⟨fun n => n + 1⟩) (μs := ⟨fun _ => ()⟩)
    (lsuOE (fun n => n + 1) (fun _ => by omega) _) rfl 0
  simp [LSU] at this

-- `Cslib.LTS.OmegaExecution.cons` idx 9: necessary (successor LTS, s = 0, t = 1, ss constant 1)
theorem oeCons9 : ¬ drop0% Cslib.LTS.OmegaExecution.cons 9 := fun H => by
  have := H (lts := LSU) (s := 0) (t := 1) (μ := ()) (ss := ⟨fun _ => 1⟩) (μs := ⟨fun _ => ()⟩)
    rfl rfl 1
  simp [LSU] at this

-- `Cslib.LTS.OmegaExecution.cons` idx 10: necessary (successor LTS, s = 0, t = 1, ss n = n + 5)
theorem oeCons10 : ¬ drop0% Cslib.LTS.OmegaExecution.cons 10 := fun H => by
  have := H (lts := LSU) (s := 0) (t := 1) (μ := ()) (ss := ⟨fun n => n + 5⟩) (μs := ⟨fun _ => ()⟩)
    rfl (lsuOE (fun n => n + 5) (fun _ => by omega) _) 0
  simp [LSU] at this

-- `Cslib.LTS.OmegaExecution.prepend_execution_tr` idx 10: necessary (successor LTS, sl = [7], μl = [], ss n = n + 1)
theorem oePT10 : ¬ drop0% Cslib.LTS.OmegaExecution.prepend_execution_tr 10 := fun H => by
  have := H (lts := LSU) (s := 0) (t := 0) (μ := ()) (μl := []) (sl := [7]) (ss := ⟨fun n => n + 1⟩)
    (μs := ⟨fun _ => ()⟩) (lsuOE (fun n => n + 1) (fun _ => by omega) _) rfl 0
  simp [LSU] at this

-- `Cslib.LTS.OmegaExecution.prepend_execution_tr` idx 11: necessary (successor LTS, sl = [0], ss constant 1)
theorem oePT11 : ¬ drop0% Cslib.LTS.OmegaExecution.prepend_execution_tr 11 := fun H => by
  have := H (lts := LSU) (s := 0) (t := 0) (μ := ()) (μl := []) (sl := [0]) (ss := ⟨fun _ => 1⟩)
    (μs := ⟨fun _ => ()⟩) (.refl 0) rfl 1
  simp [LSU] at this

-- `Cslib.LTS.OmegaExecution.prepend_execution_tr` idx 12: necessary (successor LTS, sl = [0], ss n = n)
theorem oePT12 : ¬ drop0% Cslib.LTS.OmegaExecution.prepend_execution_tr 12 := fun H => by
  have := H (lts := LSU) (s := 0) (t := 0) (μ := ()) (μl := []) (sl := [0]) (ss := ⟨fun n => n⟩)
    (μs := ⟨fun _ => ()⟩) (.refl 0) (lsuOE (fun n => n) (fun _ => by omega) _) 0
  simp [LSU] at this

-- `Cslib.LTS.OmegaExecution.prepend_execution` idx 10: necessary (successor LTS, sl = [0], ss constant 0)
theorem oePE10 : ¬ drop0% Cslib.LTS.OmegaExecution.prepend_execution 10 := fun H => by
  have := H (lts := LSU) (s := 0) (t := 0) (μl := []) (sl := [0]) (ss := ⟨fun _ => 0⟩)
    (μs := ⟨fun _ => ()⟩) (.refl 0) rfl 0
  simp [LSU] at this

-- `Cslib.LTS.OmegaExecution.prepend_execution` idx 11: necessary (successor LTS, sl = [0], ss n = n + 5)
theorem oePE11 : ¬ drop0% Cslib.LTS.OmegaExecution.prepend_execution 11 := fun H => by
  have := H (lts := LSU) (s := 0) (t := 0) (μl := []) (sl := [0]) (ss := ⟨fun n => n + 5⟩)
    (μs := ⟨fun _ => ()⟩) (.refl 0) (lsuOE (fun n => n + 5) (fun _ => by omega) _) 0
  simp [LSU] at this

-- `Cslib.LTS.OmegaExecution.append` idx 8: necessary (μl = [], s = 0, t = 1)
theorem oeApp8 : ¬ drop0% Cslib.LTS.OmegaExecution.append 8 := fun H => by
  obtain ⟨ss', _, h0, h1, _⟩ := H (lts := LSU) (s := 0) (t := 1) (μl := []) (ss := ⟨fun n => n + 1⟩)
    (μs := ⟨fun _ => ()⟩) (lsuOE (fun n => n + 1) (fun _ => by omega) _) rfl
  simp at h1; omega

-- `Cslib.LTS.OmegaExecution.append` idx 9: necessary (successor LTS, μl = [], ss constant 0)
theorem oeApp9 : ¬ drop0% Cslib.LTS.OmegaExecution.append 9 := fun H => by
  obtain ⟨ss', hω, h0, _, hd⟩ := H (lts := LSU) (s := 0) (t := 0) (μl := []) (ss := ⟨fun _ => 0⟩)
    (μs := ⟨fun _ => ()⟩) .refl rfl
  have h1 := congrArg (· 1) hd
  have h2 := hω 0
  simp [LSU] at h1 h2
  omega

-- `Cslib.LTS.OmegaExecution.append` idx 10: necessary (μl = [], s = t = 0, ss n = n + 5)
theorem oeApp10 : ¬ drop0% Cslib.LTS.OmegaExecution.append 10 := fun H => by
  obtain ⟨ss', _, h0, _, hd⟩ := H (lts := LSU) (s := 0) (t := 0) (μl := []) (ss := ⟨fun n => n + 5⟩)
    (μs := ⟨fun _ => ()⟩) .refl (lsuOE (fun n => n + 5) (fun _ => by omega) _)
  have h1 := congrArg (· 0) hd
  simp at h1
  omega

-- `Cslib.LTS.OmegaExecution.flatten_execution'` idx 8: necessary (empty LTS has no ω-execution)
theorem oeFE'8 : ¬ drop0% Cslib.LTS.OmegaExecution.flatten_execution' 8 := fun H =>
  ln0OE (H (lts := LN0) (ts := ⟨fun _ => 0⟩) (μls := ⟨fun _ => [()]⟩) (sls := ⟨fun _ => [0, 0]⟩)
    (fun _ => by simp))

-- `Cslib.LTS.OmegaExecution.flatten_execution'` idx 9: necessary (empty LTS, empty label lists)
theorem oeFE'9 : ¬ drop0% Cslib.LTS.OmegaExecution.flatten_execution' 9 := fun H =>
  ln0OE (H (lts := LN0) (ts := ⟨fun _ => 0⟩) (μls := ⟨fun _ => []⟩) (sls := ⟨fun _ => [0]⟩)
    (fun _ => .refl 0))

-- `Cslib.LTS.OmegaExecution.flatten_execution` idx 7: necessary (empty LTS has no ω-execution)
theorem oeFE7 : ¬ drop0% Cslib.LTS.OmegaExecution.flatten_execution 7 := fun H => by
  obtain ⟨_, h, _⟩ := H (lts := LN0) (ts := ⟨fun _ => 0⟩) (μls := ⟨fun _ => [()]⟩)
    (sls := ⟨fun _ => [0, 0]⟩) (fun _ => by simp)
  exact ln0OE h

-- `Cslib.LTS.OmegaExecution.flatten_execution` idx 8: necessary (empty LTS, empty label lists)
theorem oeFE8 : ¬ drop0% Cslib.LTS.OmegaExecution.flatten_execution 8 := fun H => by
  obtain ⟨_, h, _⟩ := H (lts := LN0) (ts := ⟨fun _ => 0⟩) (μls := ⟨fun _ => []⟩)
    (sls := ⟨fun _ => [0]⟩) (fun _ => .refl 0)
  exact ln0OE h

-- `Cslib.LTS.OmegaExecution.flatten_mTr` idx 6: necessary (empty LTS has no ω-execution)
theorem oeFM6 : ¬ drop0% Cslib.LTS.OmegaExecution.flatten_mTr 6 := fun H => by
  obtain ⟨_, h, _⟩ := H (lts := LN0) (ts := ⟨fun _ => 0⟩) (μls := ⟨fun _ => [()]⟩) (fun _ => by simp)
  exact ln0OE h

-- `Cslib.LTS.OmegaExecution.flatten_mTr` idx 7: necessary (empty LTS, empty label lists)
theorem oeFM7 : ¬ drop0% Cslib.LTS.OmegaExecution.flatten_mTr 7 := fun H => by
  obtain ⟨_, h, _⟩ := H (lts := LN0) (ts := ⟨fun _ => 0⟩) (μls := ⟨fun _ => []⟩) (fun _ => .refl)
  exact ln0OE h

-- `Cslib.LTS.MTr.toReflTransGen` idx 6: necessary (empty LTS, 0 to 1)
theorem mtrRTG6 : ¬ drop0% Cslib.LTS.MTr.toReflTransGen 6 := fun H => by
  rcases (H LN0 (s1 := 0) (s2 := 1) (μs := [])).cases_tail with h | ⟨_, _, _, h⟩
  · exact absurd h (by decide)
  · exact h.elim

-- `Cslib.LTS.MTr.toTransGen` idx 6: necessary (empty LTS, μs = [()])
theorem mtrTG6 : ¬ drop0% Cslib.LTS.MTr.toTransGen 6 := fun H => by
  rcases (H LN0 (s1 := 0) (s2 := 0) (μs := [()]) (by simp)) with ⟨_, h⟩ | ⟨_, ⟨_, h⟩⟩ <;> exact h.elim

-- `Cslib.LTS.MTr.toTransGen` idx 7: necessary (empty LTS, μs = [])
theorem mtrTG7 : ¬ drop0% Cslib.LTS.MTr.toTransGen 7 := fun H => by
  rcases (H LN0 (s1 := 0) (s2 := 0) (μs := []) .refl) with ⟨_, h⟩ | ⟨_, ⟨_, h⟩⟩ <;> exact h.elim

-- `Cslib.LTS.tr_setImage` idx 7: necessary (S = ∅)
theorem trSI7 : ¬ drop0% Cslib.LTS.tr_setImage 7 := fun H => by
  have := H (lts := LSU) (S := ∅) (s := 0) (μ := ()) (s' := 1) rfl
  simp [LTS.mem_setImage] at this

-- `Cslib.LTS.setImage_mono` idx 5: necessary (S = univ, T = ∅)
theorem siMono5 : ¬ drop0% Cslib.LTS.setImage_mono 5 := fun H => by
  have := H (lts := LSU) (S := Set.univ) (T := ∅) () (LTS.tr_setImage (s := 0) trivial rfl)
  simp [LTS.mem_setImage] at this

-- `Cslib.LTS.IsSimulation.comp` idx 9: necessary (r1 = r2 = ⊤; LU, LE0, LE0)
theorem simComp9 : ¬ drop0% Cslib.LTS.IsSimulation.comp 9 := fun H => by
  have := H (lts₁ := LU) (lts₂ := LE0) (lts₃ := LE0) (fun _ _ => True) (fun _ _ => True) simEE
  obtain ⟨_, h, _⟩ := this (s₁ := ()) (s₂ := ()) ⟨(), trivial, trivial⟩ () () trivial; exact h

-- `Cslib.LTS.IsSimulation.comp` idx 10: necessary (r1 = r2 = ⊤; LU, LU, LE0)
theorem simComp10 : ¬ drop0% Cslib.LTS.IsSimulation.comp 10 := fun H => by
  have := H (lts₁ := LU) (lts₂ := LU) (lts₃ := LE0) (fun _ _ => True) (fun _ _ => True) simUU
  obtain ⟨_, h, _⟩ := this (s₁ := ()) (s₂ := ()) ⟨(), trivial, trivial⟩ () () trivial; exact h

-- `Cslib.LTS.Similarity.trans` idx 10: necessary (LU, LE0, LE0)
theorem simTrans10 : ¬ drop0% Cslib.LTS.Similarity.trans 10 := fun H =>
  notSimilarUE (H (lts₁ := LU) (lts₂ := LE0) (lts₃ := LE0) (s₁ := ()) (s2 := ()) (s₃ := ())
    ⟨fun _ _ => True, trivial, simEE⟩)

-- `Cslib.LTS.Similarity.trans` idx 11: necessary (LU, LU, LE0)
theorem simTrans11 : ¬ drop0% Cslib.LTS.Similarity.trans 11 := fun H =>
  notSimilarUE (H (lts₁ := LU) (lts₂ := LU) (lts₃ := LE0) (s₁ := ()) (s2 := ()) (s₃ := ())
    ⟨fun _ _ => True, trivial, simUU⟩)

-- `Cslib.LTS.IsSimulation.sup` idx 7: necessary (r = ⊤, s = ⊥; LU vs LE0)
theorem simSup7 : ¬ drop0% Cslib.LTS.IsSimulation.sup 7 := fun H => by
  have := H (lts₁ := LU) (lts₂ := LE0) (r := fun _ _ => True) (s := fun _ _ => False)
    (fun _ _ h => h.elim)
  obtain ⟨_, h, _⟩ := this (s₁ := ()) (s₂ := ()) (Or.inl trivial) () () trivial; exact h

-- `Cslib.LTS.IsSimulation.sup` idx 8: necessary (r = ⊥, s = ⊤; LU vs LE0)
theorem simSup8 : ¬ drop0% Cslib.LTS.IsSimulation.sup 8 := fun H => by
  have := H (lts₁ := LU) (lts₂ := LE0) (r := fun _ _ => False) (s := fun _ _ => True)
    (fun _ _ h => h.elim)
  obtain ⟨_, h, _⟩ := this (s₁ := ()) (s₂ := ()) (Or.inr trivial) () () trivial; exact h

-- `Cslib.LTS.IsSimulation.sim_trace` idx 8: necessary (r = ⊤; LU vs LE0)
theorem simTr8 : ¬ drop0% Cslib.LTS.IsSimulation.sim_trace 8 := fun H => by
  obtain ⟨_, h, _⟩ := H (lts₁ := LU) (lts₂ := LE0) (r := fun _ _ => True) (s₁ := ()) (s₂ := ())
    trivial [()] () (.stepL trivial .refl)
  cases h with | stepL h _ => exact h

-- `Cslib.LTS.IsSimulation.sim_trace` idx 9: necessary (r = ⊥)
theorem simTr9 : ¬ drop0% Cslib.LTS.IsSimulation.sim_trace 9 := fun H => by
  obtain ⟨_, _, h⟩ := H (lts₁ := LU) (lts₂ := LU) (r := fun _ _ => False) (s₁ := ()) (s₂ := ())
    (fun _ _ h => h.elim) [] () .refl
  exact h

-- `Cslib.LTS.IsSimulation.sim_trace` idx 12: necessary (empty LTSs, r = Eq, μs = [], s₁' = 1)
theorem simTr12 : ¬ drop0% Cslib.LTS.IsSimulation.sim_trace 12 := fun H => by
  obtain ⟨_, h, h'⟩ := H (lts₁ := LN0) (lts₂ := LN0) (r := Eq) (s₁ := 0) (s₂ := 0)
    (fun _ _ _ _ _ h => h.elim) rfl [] 1
  rw [← h.nil_eq] at h'
  exact absurd h' (by decide)

-- `Cslib.LTS.IsSimulationMap.sim_trace` idx 10: necessary (empty LTS, f = id, s = 0, s' = 1, μs = [])
theorem simMapTr10 : ¬ drop0% Cslib.LTS.IsSimulationMap.sim_trace 10 := fun H =>
  absurd (H (lts₁ := LN0) (lts₂ := LN0) (f := id) (fun _ _ _ h => h.elim) (s := 0) (s' := 1)
    (μs := [])).nil_eq (by decide)

-- `Cslib.LTS.SimulationEquiv.symm` idx 7: necessary (LE0 vs LU)
theorem seSymm7 : ¬ drop0% Cslib.LTS.SimulationEquiv.symm 7 := fun H =>
  notSimilarUE (H (lts₁ := LE0) (lts₂ := LU) (s₁ := ()) (s2 := ())).1

-- `Cslib.LTS.SimulationEquiv.trans` idx 10: necessary (LU, LE0, LE0)
theorem seTrans10 : ¬ drop0% Cslib.LTS.SimulationEquiv.trans 10 := fun H =>
  notSimilarUE (H (lts₁ := LU) (lts₂ := LE0) (lts₃ := LE0) (s₁ := ()) (s2 := ()) (s₃ := ())
    ⟨⟨fun _ _ => True, trivial, simEE⟩, ⟨fun _ _ => True, trivial, simEE⟩⟩).1

-- `Cslib.LTS.IsSimulation.follow_internal` idx 10: necessary (T2 τ-steps false → true, E2 empty, r = Eq)
theorem simFI10 : ¬ drop0% Cslib.LTS.IsSimulation.follow_internal 10 := fun H => by
  obtain ⟨_, h, h'⟩ := H (lts₁ := T2) (lts₂ := E2) (r := Eq) (s₁ := false) (s₂ := false)
    (s₁' := true) rfl (.single ⟨rfl, rfl⟩)
  rw [← e2τ h] at h'
  exact absurd h' (by decide)

-- `Cslib.LTS.IsSimulation.follow_internal` idx 11: necessary (r = ⊥)
theorem simFI11 : ¬ drop0% Cslib.LTS.IsSimulation.follow_internal 11 := fun H => by
  obtain ⟨_, _, h'⟩ := H (lts₁ := E2) (lts₂ := E2) (r := fun _ _ => False) (s₁ := false) (s₂ := false)
    (s₁' := false) (fun _ _ h => h.elim) .refl
  exact h'

-- `Cslib.LTS.IsSimulation.follow_internal` idx 12: necessary (empty LTSs, r = Eq, s₁' = true)
theorem simFI12 : ¬ drop0% Cslib.LTS.IsSimulation.follow_internal 12 := fun H => by
  obtain ⟨_, h, h'⟩ := H (lts₁ := E2) (lts₂ := E2) (r := Eq) (s₁ := false) (s₂ := false)
    (s₁' := true) (fun _ _ _ _ _ h => h.elim) rfl
  rw [← e2τ h] at h'
  exact absurd h' (by decide)

-- `Cslib.LTS.IsSimulation.mono` idx 8: necessary (lts₁ = LE0, lts₁' = LU, lts₂ = lts₂' = LE0, r = ⊤)
theorem simMono8 : ¬ drop0% Cslib.LTS.IsSimulation.mono 8 := fun H =>
  notSimUE (H (lts₁ := LE0) (lts₁' := LU) (lts₂ := LE0) (lts₂' := LE0) le_rfl simEE)

-- `Cslib.LTS.IsSimulation.mono` idx 9: necessary (lts₁ = lts₁' = lts₂ = LU, lts₂' = LE0, r = ⊤)
theorem simMono9 : ¬ drop0% Cslib.LTS.IsSimulation.mono 9 := fun H =>
  notSimUE (H (lts₁ := LU) (lts₁' := LU) (lts₂ := LU) (lts₂' := LE0) le_rfl simUU)

-- `Cslib.LTS.IsSimulation.mono` idx 10: necessary (LU vs LE0, r = ⊤)
theorem simMono10 : ¬ drop0% Cslib.LTS.IsSimulation.mono 10 := fun H =>
  notSimUE (H (lts₁ := LU) (lts₁' := LU) (lts₂ := LE0) (lts₂' := LE0) le_rfl le_rfl)

-- `Cslib.LTS.IsSimulation.match_deterministic` idx 11: necessary (LB false → true vs LU, r s _ = (s = false))
theorem simMD11 : ¬ drop0% Cslib.LTS.IsSimulation.match_deterministic 11 := fun H => by
  have := H (lts₁ := LB) (lts₂ := LU) (r := fun s _ => s = false) (s₁ := false) (s₂ := ())
    (s₁' := true) (s₂' := ()) (μ := ()) rfl (fun _ _ _ _ => rfl) ⟨rfl, rfl⟩ trivial
  exact absurd this (by decide)

-- `Cslib.LTS.IsSimulation.follow_deterministic` idx 10: necessary (LB false → true vs LU, r s _ = (s = false))
theorem simFD10 : ¬ drop0% Cslib.LTS.IsSimulation.follow_deterministic 10 := fun H => by
  obtain ⟨_, ⟨_, h⟩, _⟩ := H (lts₁ := LB) (lts₂ := LU) (r := fun s _ => s = false) (s₁ := false)
    (s₂ := ()) (s₁' := true) (μ := ()) rfl (fun _ _ _ _ => rfl) ⟨rfl, rfl⟩
  exact absurd h (by decide)

-- `Cslib.LTS.Bounded.toTerminating` idx 3: necessary (self-loop LTS)
theorem bTerm3 : ¬ drop0% Cslib.LTS.Bounded.toTerminating 3 := fun H =>
  Example.selfLoopLTS_not_acyclic (LTS.Terminating.toAcyclic _ (H (lts := Example.selfLoopLTS)))

-- `Cslib.LTS.bounded_terminating` idx 3: necessary (self-loop LTS)
theorem bTermI3 : ¬ drop0% Cslib.LTS.bounded_terminating 3 := fun H =>
  Example.selfLoopLTS_not_acyclic (LTS.Terminating.toAcyclic _ (H (lts := Example.selfLoopLTS)))

-- `Cslib.LTS.Terminating.toAcyclic` idx 3: necessary (self-loop LTS)
theorem tAcyc3 : ¬ drop0% Cslib.LTS.Terminating.toAcyclic 3 := fun H =>
  Example.selfLoopLTS_not_acyclic (H (lts := Example.selfLoopLTS))

-- `Cslib.LTS.terminating_acyclic` idx 3: necessary (self-loop LTS)
theorem tAcycI3 : ¬ drop0% Cslib.LTS.terminating_acyclic 3 := fun H =>
  Example.selfLoopLTS_not_acyclic (H (lts := Example.selfLoopLTS))

-- `Cslib.LTS.Acyclic.toBoundedUpTo` idx 3: necessary (successor LTS on ℕ, Nat.card ℕ = 0)
theorem aBUT3 : ¬ drop0% Cslib.LTS.Acyclic.toBoundedUpTo 3 := fun H => by
  have := H (lts := Example.successorLTS) inferInstance 0 [] 0 .refl
  simp at this

-- `Cslib.LTS.Acyclic.toBoundedUpTo` idx 4: necessary (self-loop LTS, bound Nat.card Unit = 1)
theorem aBUT4 : ¬ drop0% Cslib.LTS.Acyclic.toBoundedUpTo 4 := fun H => by
  have := H (lts := Example.selfLoopLTS) () [()] () (.stepL trivial .refl)
  simp at this

-- `Cslib.LTS.Acyclic.toBounded` idx 3: necessary (successor LTS on ℕ)
theorem aB3 : ¬ drop0% Cslib.LTS.Acyclic.toBounded 3 := fun H =>
  Example.successorLTS_not_terminating
    (LTS.Bounded.toTerminating _ (H (lts := Example.successorLTS) inferInstance))

-- `Cslib.LTS.Acyclic.toBounded` idx 4: necessary (self-loop LTS)
theorem aB4 : ¬ drop0% Cslib.LTS.Acyclic.toBounded 4 := fun H =>
  Example.selfLoopLTS_not_acyclic (LTS.Terminating.toAcyclic _
    (LTS.Bounded.toTerminating _ (H (lts := Example.selfLoopLTS))))

-- `Cslib.LTS.Acyclic.toTerminating` idx 3: necessary (successor LTS on ℕ)
theorem aT3 : ¬ drop0% Cslib.LTS.Acyclic.toTerminating 3 := fun H =>
  Example.successorLTS_not_terminating (H (lts := Example.successorLTS) inferInstance)

-- `Cslib.LTS.Acyclic.toTerminating` idx 4: necessary (self-loop LTS)
theorem aT4 : ¬ drop0% Cslib.LTS.Acyclic.toTerminating 4 := fun H =>
  Example.selfLoopLTS_not_acyclic (LTS.Terminating.toAcyclic _ (H (lts := Example.selfLoopLTS)))

end W3c4

namespace W3c4
open Cslib Cslib.LTS

theorem trU : [()] ∈ LU.traces () := ⟨(), .stepL trivial .refl⟩
theorem ntrE : [()] ∉ LE0.traces () := fun ⟨_, h⟩ => by cases h with | stepL h _ => exact h
theorem notTEUE : ¬ LU.TraceEq LE0 () () := fun h => ntrE (h ▸ trU)

-- NB: 0 -t-> 1, 0 -t-> 4, 1 -t-> 2, 4 -f-> 3 ; DB (deterministic): 0 -t-> 1, 1 -t-> 2, 1 -f-> 3
def NB : LTS ℕ Bool := ⟨fun s μ t => (s = 0 ∧ μ = true ∧ (t = 1 ∨ t = 4)) ∨ (s = 1 ∧ μ = true ∧ t = 2) ∨
  (s = 4 ∧ μ = false ∧ t = 3)⟩
def DB : LTS ℕ Bool := ⟨fun s μ t => (s = 0 ∧ μ = true ∧ t = 1) ∨ (s = 1 ∧ μ = true ∧ t = 2) ∨
  (s = 1 ∧ μ = false ∧ t = 3)⟩
instance DBdet : DB.Deterministic := ⟨by
  intro s μ a b ha hb
  cases μ <;> simp [DB] at ha hb <;> omega⟩

theorem teBD : NB.TraceEq DB 0 0 := by
  ext μs
  rcases μs with _ | ⟨a, _ | ⟨b, _ | ⟨c, μs⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;> (try cases c) <;>
    simp [LTS.mem_traces_iff, LTS.MTr.cons_iff, NB, DB]

theorem notSimDN : ¬ DB.Similarity NB 0 0 := fun ⟨r, hr, hs⟩ => by
  obtain ⟨s, hs1, hr1⟩ := hs hr true 1 (by simp [DB])
  simp [NB] at hs1
  rcases hs1 with rfl | rfl
  · obtain ⟨_, h, _⟩ := hs hr1 false 3 (by simp [DB]); simp [NB] at h
  · obtain ⟨_, h, _⟩ := hs hr1 true 2 (by simp [DB]); simp [NB] at h

theorem notTE11 : ¬ NB.TraceEq DB 1 1 := fun h => by
  have : [false] ∈ DB.traces 1 := ⟨3, .stepL (by simp [DB]) .refl⟩
  rw [← h] at this
  obtain ⟨_, h'⟩ := this
  cases h' with | stepL h _ => simp [NB] at h

theorem notTE14 : ¬ DB.TraceEq NB 1 4 := fun h => by
  have : [true] ∈ DB.traces 1 := ⟨2, .stepL (by simp [DB]) .refl⟩
  rw [h] at this
  obtain ⟨_, h'⟩ := this
  cases h' with | stepL h _ => simp [NB] at h

theorem notTE12 : ¬ DB.TraceEq DB 1 2 := fun h => by
  have : [true] ∈ DB.traces 1 := ⟨2, .stepL (by simp [DB]) .refl⟩
  rw [h] at this
  obtain ⟨_, h'⟩ := this
  cases h' with | stepL h _ => simp [DB] at h

-- `Cslib.LTS.IsSimulation.traces_subset` idx 8: necessary (r = ⊤; LU vs LE0)
theorem trSub8 : ¬ drop0% Cslib.LTS.IsSimulation.traces_subset 8 := fun H =>
  ntrE (H (lts₁ := LU) (lts₂ := LE0) (r := fun _ _ => True) (s₁ := ()) (s₂ := ()) trivial trU)

-- `Cslib.LTS.IsSimulation.traces_subset` idx 9: necessary (r = ⊥; LU vs LE0)
theorem trSub9 : ¬ drop0% Cslib.LTS.IsSimulation.traces_subset 9 := fun H =>
  ntrE (H (lts₁ := LU) (lts₂ := LE0) (r := fun _ _ => False) (s₁ := ()) (s₂ := ())
    (fun _ _ h => h.elim) trU)

-- `Cslib.LTS.TraceEq.trans` idx 10: necessary (LU, LE0, LE0)
theorem teTrans10 : ¬ drop0% Cslib.LTS.TraceEq.trans 10 := fun H =>
  notTEUE (H (lts₁ := LU) (lts₂ := LE0) (lts₃ := LE0) (s₁ := ()) (s₂ := ()) (s₃ := ()) rfl)

-- `Cslib.LTS.TraceEq.trans` idx 11: necessary (LU, LU, LE0)
theorem teTrans11 : ¬ drop0% Cslib.LTS.TraceEq.trans 11 := fun H =>
  notTEUE (H (lts₁ := LU) (lts₂ := LU) (lts₃ := LE0) (s₁ := ()) (s₂ := ()) (s₃ := ()) rfl)

-- `Cslib.LTS.TraceEq.exists_mTr_of_mTr` idx 9: necessary (LU vs LE0, μs = [()])
theorem teMTr9 : ¬ drop0% Cslib.LTS.TraceEq.exists_mTr_of_mTr 9 := fun H => by
  obtain ⟨s, h⟩ := H (lts₁ := LU) (lts₂ := LE0) (s₁ := ()) (s₂ := ()) (μs := [()]) (s₁' := ())
    (.stepL trivial .refl)
  exact ntrE ⟨s, h⟩

-- `Cslib.LTS.TraceEq.exists_mTr_of_mTr` idx 10: necessary (LE0 vs LE0, μs = [()])
theorem teMTr10 : ¬ drop0% Cslib.LTS.TraceEq.exists_mTr_of_mTr 10 := fun H => by
  obtain ⟨s, h⟩ := H (lts₁ := LE0) (lts₂ := LE0) (s₁ := ()) (s₂ := ()) (μs := [()]) (s₁' := ()) rfl
  exact ntrE ⟨s, h⟩

-- `Cslib.LTS.TraceEq.exists_tr_of_tr` idx 10: necessary (LE0 vs LE0)
theorem teTr10 : ¬ drop0% Cslib.LTS.TraceEq.exists_tr_of_tr 10 := fun H => by
  obtain ⟨s, h⟩ := H (lts₁ := LE0) (lts₂ := LE0) (s₁ := ()) (s₂ := ()) (μ := ()) (s₁' := ()) rfl
  exact h

-- `Cslib.LTS.TraceEq.traceEq_of_tr_of_tr` idx 11: necessary (DB deterministic vs NB, 0 -t-> 1 vs 0 -t-> 4)
theorem teTrTr11 : ¬ drop0% Cslib.LTS.TraceEq.traceEq_of_tr_of_tr 11 := fun H =>
  notTE14 (H (lts₁ := DB) (lts₂ := NB) (s₁ := 0) (s₂ := 0) (μ := true) (s₁' := 1) (s₂' := 4)
    teBD.symm (by simp [DB]) (by simp [NB]))

-- `Cslib.LTS.TraceEq.traceEq_of_tr_of_tr` idx 12: necessary (DB, 0 -t-> 1 and 1 -t-> 2)
theorem teTrTr12 : ¬ drop0% Cslib.LTS.TraceEq.traceEq_of_tr_of_tr 12 := fun H =>
  notTE12 (H (lts₁ := DB) (lts₂ := DB) (s₁ := 0) (s₂ := 1) (μ := true) (s₁' := 1) (s₂' := 2)
    (by simp [DB]) (by simp [DB]))

-- `Cslib.LTS.TraceEq.traceEq_of_tr_of_tr` idx 13: necessary (DB, s₁ = s₂ = 0, s₁' = 2, s₂' = 1)
theorem teTrTr13 : ¬ drop0% Cslib.LTS.TraceEq.traceEq_of_tr_of_tr 13 := fun H =>
  notTE12 (H (lts₁ := DB) (lts₂ := DB) (s₁ := 0) (s₂ := 0) (μ := true) (s₁' := 2) (s₂' := 1)
    rfl (by simp [DB])).symm

-- `Cslib.LTS.TraceEq.traceEq_of_tr_of_tr` idx 14: necessary (DB, s₁ = s₂ = 0, s₁' = 1, s₂' = 2)
theorem teTrTr14 : ¬ drop0% Cslib.LTS.TraceEq.traceEq_of_tr_of_tr 14 := fun H =>
  notTE12 (H (lts₁ := DB) (lts₂ := DB) (s₁ := 0) (s₂ := 0) (μ := true) (s₁' := 1) (s₂' := 2)
    rfl (by simp [DB]))

-- `Cslib.LTS.Deterministic.isSimulation_traceEq` idx 5: necessary (NB vs DB: NB 0 -t-> 1 unmatched)
theorem detSimTE5 : ¬ drop0% Cslib.LTS.Deterministic.isSimulation_traceEq 5 := fun H => by
  obtain ⟨s, hs, h⟩ := H (lts₁ := NB) (lts₂ := DB) teBD true 1 (by simp [NB])
  have : s = 1 := by simp [DB] at hs; omega
  subst this
  exact notTE11 h

-- `Cslib.LTS.Deterministic.isSimulation_traceEq` idx 6: necessary (DB vs NB, trace equivalent, not similar)
theorem detSimTE6 : ¬ drop0% Cslib.LTS.Deterministic.isSimulation_traceEq 6 := fun H =>
  notSimDN ⟨_, teBD.symm, H (lts₁ := DB) (lts₂ := NB)⟩

-- `Cslib.LTS.SimulationEquiv.traceEq` idx 7: necessary (LU vs LE0)
theorem seTE7 : ¬ drop0% Cslib.LTS.SimulationEquiv.traceEq 7 := fun H =>
  notTEUE (H (lts₁ := LU) (lts₂ := LE0) (s₁ := ()) (s₂ := ()))

-- `Cslib.LTS.Deterministic.traceEq_iff_simulationEquiv` idx 5: necessary (NB vs DB)
theorem detTESE5 : ¬ drop0% Cslib.LTS.Deterministic.traceEq_iff_simulationEquiv 5 := fun H =>
  notSimDN ((H (lts₁ := NB) (lts₂ := DB) 0 0).mp teBD).2

-- `Cslib.LTS.Deterministic.traceEq_iff_simulationEquiv` idx 6: necessary (DB vs NB)
theorem detTESE6 : ¬ drop0% Cslib.LTS.Deterministic.traceEq_iff_simulationEquiv 6 := fun H =>
  notSimDN ((H (lts₁ := DB) (lts₂ := NB) 0 0).mp teBD.symm).1

-- `Cslib.LTS.unionSum_mTr_inl` idx 8: necessary (y = inr ())
theorem usInl8 : ¬ drop0% Cslib.LTS.unionSum_mTr_inl 8 := fun H => by
  obtain ⟨_, h, _⟩ := H (lts1 := LE0) (lts2 := LE0) (s := ()) (μs := []) (y := Sum.inr ())
  cases h

-- `Cslib.LTS.unionSum_mTr_inr` idx 8: necessary (y = inl ())
theorem usInr8 : ¬ drop0% Cslib.LTS.unionSum_mTr_inr 8 := fun H => by
  obtain ⟨_, h, _⟩ := H (lts1 := LE0) (lts2 := LE0) (s := ()) (μs := []) (y := Sum.inl ())
  cases h

-- `Cslib.LawfulCongruence.toIsEquiv` idx 4: necessary (empty relation on Unit)
theorem lcEquiv4 : ¬ drop0% Cslib.LawfulCongruence.toIsEquiv 4 := fun H => by
  have := @H Unit (fun _ _ => False) ⟨⟩ ⟨fun (_ : Unit) x => x⟩
  exact refl_of (fun (_ _ : Unit) => False) ()

-- `Cslib.LawfulCongruence.covariant` idx 4: necessary (r a b := a = false ∧ b = true, constant context false)
theorem lcCov4 : ¬ drop0% Cslib.LawfulCongruence.covariant 4 := fun H => by
  have := (@H Bool (fun a b => a = false ∧ b = true) ⟨⟩
    ⟨fun (_ : Unit) (_ : Bool) => false⟩).elim () (n₁ := false) (n₂ := true) ⟨rfl, rfl⟩
  exact Bool.false_ne_true this.2

end W3c4

namespace W3c4
open Cslib Cslib.CCS

abbrev P0 : Process Unit Unit := .nil
abbrev P1 : Process Unit Unit := .pre .τ .nil
-- nondeterministic: two τ-derivatives nil and τ.nil
abbrev P2 : Process Unit Unit := .choice (.pre .τ .nil) (.pre .τ (.pre .τ .nil))

theorem ltr {d : Unit → Option (Process Unit Unit)} {p q : Process Unit Unit} {μ : Act Unit}
    (h : Tr (defs := d) p μ q) : (lts (defs := d)).Tr p μ q := by unfold lts; exact h

theorem nb {d : Unit → Option (Process Unit Unit)} : ¬ (lts (defs := d)).HomBisimilarity P1 P0 :=
  fun h => by
    obtain ⟨_, htr, _⟩ := LTS.Bisimilarity.follow_fst (μ := Act.τ) (s₁' := .nil) h (ltr Tr.pre)
    unfold lts at htr
    cases htr

-- `Cslib.CCS.Act.Co.symm` idx 3: necessary (μ = μ' = τ)
theorem coSymm3 : ¬ drop0% Cslib.CCS.Act.Co.symm 3 := fun H =>
  nomatch @H Unit .τ .τ

-- `Cslib.CCS.Act.co_isVisible` idx 3: necessary (μ = μ' = τ)
theorem coVis3 : ¬ drop0% Cslib.CCS.Act.co_isVisible 3 := fun H =>
  nomatch (@H Unit .τ .τ).1

-- `Cslib.CCS.bisimilarity_congr_pre` idx 6: necessary (p = τ.0, q = 0, μ = τ)
theorem bcPre6 : ¬ drop0% Cslib.CCS.bisimilarity_congr_pre 6 := fun H => by
  have h := H (defs := fun _ => none) (p := P1) (q := P0) (μ := .τ)
  obtain ⟨q', htr, h'⟩ := LTS.Bisimilarity.follow_fst (μ := Act.τ) (s₁' := P1) h (ltr Tr.pre)
  obtain ⟨_, rfl⟩ := CCS.pre_tr htr
  exact nb h'

-- `Cslib.CCS.bisimilarity_congr_res` idx 6: necessary (p = τ.0, q = 0)
theorem bcRes6 : ¬ drop0% Cslib.CCS.bisimilarity_congr_res 6 := fun H => by
  have h := H (defs := fun _ => none) (p := P1) (q := P0) (a := ())
  obtain ⟨_, htr, _⟩ := LTS.Bisimilarity.follow_fst (μ := Act.τ) (s₁' := .res () .nil) h
    (ltr (Tr.res (by simp) (by simp) Tr.pre))
  exact CCS.not_tr_of_terminated (.res .nil) htr

-- `Cslib.CCS.bisimilarity_congr_choice` idx 6: necessary (p = τ.0, q = r = 0)
theorem bcChoice6 : ¬ drop0% Cslib.CCS.bisimilarity_congr_choice 6 := fun H => by
  have h := H (defs := fun _ => none) (p := P1) (q := P0) (r := P0)
  obtain ⟨_, htr, _⟩ := LTS.Bisimilarity.follow_fst (μ := Act.τ) (s₁' := .nil) h (ltr (Tr.choiceL Tr.pre))
  exact CCS.not_tr_of_terminated (.choice .nil .nil) htr

-- `Cslib.CCS.bisimilarity_congr_par` idx 6: necessary (p = τ.0, q = r = 0)
theorem bcPar6 : ¬ drop0% Cslib.CCS.bisimilarity_congr_par 6 := fun H => by
  have h := H (defs := fun _ => none) (p := P1) (q := P0) (r := P0)
  obtain ⟨_, htr, _⟩ := LTS.Bisimilarity.follow_fst (μ := Act.τ) (s₁' := .par .nil .nil) h
    (ltr (Tr.parL Tr.pre))
  exact CCS.not_tr_of_terminated (.par .nil .nil) htr

-- `Cslib.CCS.bisimilarity_is_congruence` idx 6: necessary (hole context, p = τ.0, q = 0)
theorem bcCong6 : ¬ drop0% Cslib.CCS.bisimilarity_is_congruence 6 := fun H =>
  nb (H (defs := fun _ => none) P1 P0 .hole)

-- `Cslib.CCS.not_tr_of_terminated` idx 6: necessary (p = τ.0)
theorem ntTerm6 : ¬ drop0% Cslib.CCS.not_tr_of_terminated 6 := fun H =>
  H (defs := fun _ => none) (p := P1) (μ := .τ) (p' := .nil) (ltr Tr.pre)

-- `Cslib.CCS.pre_tr` idx 7: necessary (μ = τ, μ' = name ())
theorem preTr7 : ¬ drop0% Cslib.CCS.pre_tr 7 := fun H =>
  nomatch (H (defs := fun (_ : Unit) => none) (μ := .τ) (p := P0) (μ' := .name ()) (p' := P0)).1

-- `Cslib.CCS.const_tr` idx 6: necessary (no definitions)
theorem constTr6 : ¬ drop0% Cslib.CCS.const_tr 6 := fun H => by
  obtain ⟨_, h, _⟩ := H (defs := fun (_ : Unit) => (none : Option (Process Unit Unit))) (k := ())
    (μ := .τ) (p' := .nil)
  cases h

-- `Cslib.CCS.const_deterministicStateLabel` idx 6: necessary (p = 0, but the constant is defined as τ.0 + τ.τ.0)
theorem constDet6 : ¬ drop0% Cslib.CCS.const_deterministicStateLabel 6 := fun H => by
  have := H (defs := fun _ => some P2) (k := ()) (p := P0) (μ := .τ) (fun _ _ h _ => by cases h)
    _ _ (ltr (Tr.const rfl (Tr.choiceL Tr.pre))) (ltr (Tr.const rfl (Tr.choiceR Tr.pre)))
  cases this

-- `Cslib.CCS.const_deterministicStateLabel` idx 7: necessary (constant defined as τ.0 + τ.τ.0)
theorem constDet7 : ¬ drop0% Cslib.CCS.const_deterministicStateLabel 7 := fun H => by
  have := H (defs := fun _ => some P2) (k := ()) (p := P2) (μ := .τ) rfl
    _ _ (ltr (Tr.const rfl (Tr.choiceL Tr.pre))) (ltr (Tr.const rfl (Tr.choiceR Tr.pre)))
  cases this

-- `Cslib.CCS.res_deterministicStateLabel` idx 6: necessary (p = τ.0 + τ.τ.0)
theorem resDet6 : ¬ drop0% Cslib.CCS.res_deterministicStateLabel 6 := fun H => by
  have := H (defs := fun (_ : Unit) => none) (p := P2) (μ := .τ) (μ' := ())
    _ _ (ltr (Tr.res (by simp) (by simp) (Tr.choiceL Tr.pre))) (ltr (Tr.res (by simp) (by simp) (Tr.choiceR Tr.pre)))
  cases this

end W3c4

namespace W3c4
open Cslib Cslib.SKI Relation

theorem blInj {u v : Bool} {a : SKI} (h1 : IsBool u a) (h2 : IsBool v a) : u = v :=
  isBool_injective _ _ _ _ h1 h2 ⟨_, .refl, .refl⟩

-- `Cslib.SKI.Polynomial.elimVar_correct` idx 3: necessary (dependent; n = 0, ys = [I])
theorem evc3 : ¬ indep0% Cslib.SKI.Polynomial.elimVar_correct 3 := fun H =>
  absurd (H (n := 0) (.var 0) (ys := [SKI.I]) SKI.I) (by simp)

-- `Cslib.SKI.Polynomial.toSKI_correct` idx 3: necessary (dependent; n = 0, xs = [I])
theorem tsc3 : ¬ indep0% Cslib.SKI.Polynomial.toSKI_correct 3 := fun H =>
  absurd (H (n := 0) (.term SKI.I) [SKI.I]) (by simp)

-- `Cslib.SKI.B_tail_mred` idx 4: necessary (B K K K reduces to the normal forms K (K K) and, by assumption, K S)
theorem btm4 : ¬ drop0% Cslib.SKI.B_tail_mred 4 := fun H => by
  have := unique_normal_form (B_def SKI.K SKI.K SKI.K) (H SKI.K SKI.K SKI.K SKI.S)
    (by simp [RedexFree]) (by simp [RedexFree])
  simp at this

-- `Cslib.SKI.C_head_mred` idx 4: necessary (C K K K reduces to K and, by assumption, to S K)
theorem chm4 : ¬ drop0% Cslib.SKI.C_head_mred 4 := fun H => by
  have := unique_normal_form ((C_def SKI.K SKI.K SKI.K).trans (MRed.K _ _)) (H SKI.K SKI.K SKI.K SKI.S)
    (by simp [RedexFree]) (by simp [RedexFree])
  simp at this

-- `Cslib.SKI.isBool_trans` idx 3: necessary (a = FF, a' = TT, u = true)
theorem ibt3 : ¬ drop0% Cslib.SKI.isBool_trans 3 := fun H =>
  absurd (blInj (H true FF TT TT_correct) FF_correct) (by decide)

-- `Cslib.SKI.isBool_trans` idx 4: necessary (a = a' = FF, u = true)
theorem ibt4 : ¬ drop0% Cslib.SKI.isBool_trans 4 := fun H =>
  absurd (blInj (H true FF FF .refl) FF_correct) (by decide)

-- `Cslib.SKI.cond_correct` idx 4: necessary (x = K, y = S: Cond K S I would reduce to both)
theorem cc4 : ¬ drop0% Cslib.SKI.cond_correct 4 := fun H => by
  have := unique_normal_form (H SKI.I SKI.K SKI.S true) (H SKI.I SKI.K SKI.S false)
    (by simp [RedexFree]) (by simp [RedexFree])
  simp at this

-- `Cslib.SKI.neg_correct` idx 2: necessary (Neg I would be both booleans)
theorem nc2 : ¬ drop0% Cslib.SKI.neg_correct 2 := fun H =>
  absurd (blInj (H SKI.I true) (H SKI.I false)) (by decide)

-- `Cslib.SKI.and_correct` idx 4: necessary (b = TT: And I TT would be both booleans)
theorem ac4 : ¬ drop0% Cslib.SKI.and_correct 4 := fun H =>
  absurd (blInj (H SKI.I TT true true TT_correct) (H SKI.I TT false true TT_correct)) (by decide)

-- `Cslib.SKI.and_correct` idx 5: necessary (a = TT: And TT I would be both booleans)
theorem ac5 : ¬ drop0% Cslib.SKI.and_correct 5 := fun H =>
  absurd (blInj (H TT SKI.I true true TT_correct) (H TT SKI.I true false TT_correct)) (by decide)

-- `Cslib.SKI.or_correct` idx 4: necessary (b = FF: Or I FF would be both booleans)
theorem oc4 : ¬ drop0% Cslib.SKI.or_correct 4 := fun H =>
  absurd (blInj (H SKI.I FF true false FF_correct) (H SKI.I FF false false FF_correct)) (by decide)

-- `Cslib.SKI.or_correct` idx 5: necessary (a = FF: Or FF I would be both booleans)
theorem oc5 : ¬ drop0% Cslib.SKI.or_correct 5 := fun H =>
  absurd (blInj (H FF SKI.I false true FF_correct) (H FF SKI.I false false FF_correct)) (by decide)

end W3c4
