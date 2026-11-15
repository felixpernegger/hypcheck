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

/-! ## Joint removal of two hypotheses (J1c0)

`drop2% T i j` / `drop2_0% T i j`: `T` with its two non-dependent Prop binders `i < j` dropped
(`_0`: universes set to `0`, for refutations only).
`indep2% T i j` / `indep2_0% T i j`: for two dependent Prop binders (the conclusion or later
binders mention them): `∀ rest, Hᵢ ∧ Hⱼ`, where `rest` are the binders that depend on neither;
"jointly removable" means both are derivable from `rest`. -/

def hcDrop2 (T : Ident) (i j : Nat) (zero : Bool) : TermElabM Lean.Expr := do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us ← if zero then pure (ci.levelParams.map fun _ => Level.zero)
    else ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    unless i < j && j < xs.size do throwError "need i < j < {xs.size}"
    for k in [i, j] do
      let x := xs[k]!
      unless ← isProp (← inferType x) do throwError "binder {k} of {n} is not a Prop"
      for l in [k+1:xs.size] do
        if (← inferType xs[l]!).containsFVar x.fvarId! then throwError "binder {k} of {n} is dependent"
      if body.containsFVar x.fvarId! then throwError "binder {k} of {n} is dependent"
    mkForallFVars (xs.filter fun y => y != xs[i]! && y != xs[j]!) body

def hcIndep2 (T : Ident) (i j : Nat) (zero : Bool) : TermElabM Lean.Expr := do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us ← if zero then pure (ci.levelParams.map fun _ => Level.zero)
    else ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    unless i < j && j < xs.size do throwError "need i < j < {xs.size}"
    let xi := xs[i]!; let xj := xs[j]!
    for x in [xi, xj] do
      unless ← isProp (← inferType x) do throwError "binder of {n} is not a Prop"
    let hi ← inferType xi; let hj ← inferType xj
    if hj.containsFVar xi.fvarId! then throwError "Hⱼ mentions binder {i}"
    let mut dep := #[xi, xj]
    for l in [i+1:xs.size] do
      if l == j then continue
      let t ← inferType xs[l]!
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push xs[l]!
    unless dep.size > 2 || body.containsFVar xi.fvarId! || body.containsFVar xj.fvarId! do
      throwError "neither binder is dependent: use drop2%"
    mkForallFVars (xs.filter (!dep.contains ·)) (mkAnd hi hj)

elab "drop2% " T:ident i:num j:num : term => hcDrop2 T i.getNat j.getNat false
elab "drop2_0% " T:ident i:num j:num : term => hcDrop2 T i.getNat j.getNat true
elab "indep2% " T:ident i:num j:num : term => hcIndep2 T i.getNat j.getNat false
elab "indep2_0% " T:ident i:num j:num : term => hcIndep2 T i.getNat j.getNat true

/-! ## Helpers (copied from checks/U1c0Hand.lean: an image-infinite pair of LTSs related at omega but not bisimilar) -/

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

namespace J2c0
/-- In `L1`, `r` steps to `d 0`; whatever `L2`-successor of `r` matches it is not omega-related to `d 0`, so `r` and
`r` are not bisimilar although they are omega-related (`rr`). -/
theorem notBis : ¬ L1.Bisimilarity L2 St.r St.r := fun hb => by
  obtain ⟨t, ht, hr⟩ := hb.follow_fst (μ := false) (s₁' := St.d 0) (Or.inr ⟨rfl, rfl, rfl⟩)
  exact noMatch t ht (hr.approx _)
end J2c0
open J2c0

-- `Cslib.LTS.BisimilarityApprox.isBisimulation_omega` idx 5, 6: not jointly removable
theorem ibo56 : ¬ drop2_0% Cslib.LTS.BisimilarityApprox.isBisimulation_omega 5 6 := fun h =>
  notBis ⟨_, rr, @h St St Bool L1 L2⟩

-- `Cslib.LTS.BisimilarityApprox.bisimilarity_of_omega` idx 7, 8: not jointly removable
theorem bo78 : ¬ drop2_0% Cslib.LTS.BisimilarityApprox.bisimilarity_of_omega 7 8 := fun h =>
  notBis (@h St St Bool L1 L2 St.r St.r rr)

-- `Cslib.LTS.BisimilarityApprox.omega_iff_bisimilarity` idx 7, 8: not jointly removable
theorem oi78 : ¬ drop2_0% Cslib.LTS.BisimilarityApprox.omega_iff_bisimilarity 7 8 := fun h =>
  notBis ((@h St St Bool L1 L2 St.r St.r).mp rr)

-- `Cslib.LTS.BisimilarityApprox.omega_eq_bisimilarity` idx 5, 6: not jointly removable
theorem oe56 : ¬ drop2_0% Cslib.LTS.BisimilarityApprox.omega_eq_bisimilarity 5 6 := fun h =>
  notBis (congrFun (congrFun (@h St St Bool L1 L2) St.r) St.r ▸ rr)

-- `Cslib.LTS.BisimilarityApprox.eq_bisimilarity` idx 5, 6: not jointly removable
theorem eb56 : ¬ drop2_0% Cslib.LTS.BisimilarityApprox.eq_bisimilarity 5 6 := fun h =>
  notBis (congrFun (congrFun (h (lts₁ := L1) (lts₂ := L2) (o := (Ordinal.omega0 : Ordinal)) le_rfl) St.r) St.r ▸ rr)

-- `Cslib.LTS.BisimilarityApprox.iff_bisimilarity` idx 7, 8: not jointly removable
theorem ib78 : ¬ drop2_0% Cslib.LTS.BisimilarityApprox.iff_bisimilarity 7 8 := fun h =>
  notBis ((h (lts₁ := L1) (lts₂ := L2) (s₁ := St.r) (s₂ := St.r) (o := (Ordinal.omega0 : Ordinal)) le_rfl).mp rr)
