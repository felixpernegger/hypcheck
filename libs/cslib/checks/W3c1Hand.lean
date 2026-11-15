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

namespace W3c1

section
open Cslib.Crypto.PRG
-- generators
def gE : Generator Empty Unit := ⟨Empty.elim⟩
def gU : Generator Unit Unit := ⟨id⟩
def gT : Generator Unit Bool := ⟨fun _ => true⟩
noncomputable def advT {α : Type} : Adversary α := fun _ => PMF.pure true
-- gT is expanding, so not perfectly secure
theorem gT_exp : gT.IsExpanding := by simp [Generator.IsExpanding]
theorem gT_ns : ¬ gT.Secure (fun _ => True) 0 := Generator.not_secure_zero_of_isExpanding _ gT_exp
end

section
open Cslib.Crypto.PRG Cslib.Crypto.PRG.Generator Cslib.Probability.PMF
-- a test reading only the first (second) component of a pair has the advantage of the test itself
theorem advFst {S O : Type} [Fintype S] [Nonempty S] [Fintype O] [Nonempty O] (G : Generator S O)
    (B : Adversary O) : G.prod.advantage (fun p => B p.1) = G.advantage B := by
  have h1 : G.prod.realExperiment (fun p => B p.1) = G.realExperiment B := by
    rw [realExperiment_prod]; congr 1; funext y; simp [leftReduction, PMF.bind_const]
  have h2 : idealExperiment (fun p : O × O => B p.1) = idealExperiment B := by
    rw [← idealExperiment_rightReduction]
    show (uniformOfFintype O).bind (fun _ => (uniformOfFintype O).bind B) = _
    rw [PMF.bind_const]; rfl
  simp only [advantage, h1, h2]
theorem advSnd {S O : Type} [Fintype S] [Nonempty S] [Fintype O] [Nonempty O] (G : Generator S O)
    (B : Adversary O) : G.prod.advantage (fun p => B p.2) = G.advantage B := by
  have h1 : G.prod.realExperiment (fun p => B p.2) = G.realExperiment B := by
    rw [realExperiment_prod]
    show G.outputDist.bind (fun _ => G.outputDist.bind B) = _
    rw [PMF.bind_const]; rfl
  have h2 : idealExperiment (fun p : O × O => B p.2) = idealExperiment B := by
    rw [← idealExperiment_rightReduction]; congr 1; funext y
    simp [rightReduction, PMF.bind_const]
  simp only [advantage, h1, h2]
theorem gT_rng : 0 < gT.advantage gT.rangeAdversary := by
  have := gT.one_sub_card_div_le_advantage_rangeAdversary
  simp at this; linarith
end

section
open Cslib.Crypto.PRG Cslib.Crypto.PRG.Generator
noncomputable def A1 : Adversary (Bool × Bool) := fun p => gT.rangeAdversary p.1
noncomputable def A2 : Adversary (Bool × Bool) := fun p => gT.rangeAdversary p.2
theorem rA1 : gT.advantage (rightReduction A1) ≤ 0 := by
  have : rightReduction A1 = fun _ => (Cslib.Probability.PMF.uniformOfFintype Bool).bind gT.rangeAdversary := rfl
  rw [this, advantage_const]
theorem lA2 : gT.advantage (gT.leftReduction A2) ≤ 0 := by
  have : gT.leftReduction A2 = fun _ => gT.outputDist.bind gT.rangeAdversary := rfl
  rw [this, advantage_const]
end

section
open Cslib.Crypto.Protocols.Commitment
-- trivial scheme: constant commitment, always accepts (perfectly hiding, not binding)
noncomputable def sc0 : Scheme Bool Unit Unit where
  commit _ := PMF.pure ((), ())
  verify _ _ _ := true
  correct _ _ _ _ := rfl
-- identity scheme: commitment = message (perfectly binding, not hiding)
noncomputable def scB : Scheme Bool Bool Unit where
  commit m := PMF.pure (m, ())
  verify m c _ := m == c
  correct m c o h := by simp at h; simp [h]
-- commitment always true, accepts only commitment true
noncomputable def scT : Scheme Unit Bool Unit where
  commit _ := PMF.pure (true, ())
  verify _ c _ := c
  correct _ c _ h := by simp at h; exact h
theorem scB_bind : scB.PerfectlyBinding := by
  intro c m₀ o₀ m₁ o₁ h₀ h₁; simp [Scheme.Accepts, scB] at h₀ h₁; rw [h₀, h₁]
theorem sc0_hide : sc0.PerfectlyHiding := fun _ _ => rfl
theorem sc0_nbind : ¬ sc0.PerfectlyBinding := fun h => absurd (h () true () false () rfl rfl) (by decide)
theorem bool_nss : ¬ Subsingleton Bool := fun h => absurd (@Subsingleton.elim Bool h true false) (by decide)
end

section
open Cslib.Crypto.Protocols.PerfectSecrecy
-- identity encryption on Bool with a single key
noncomputable def idS : EncScheme Bool Unit Bool :=
  EncScheme.ofPure (PMF.pure ()) (fun _ m => m) (fun _ c => c) (fun _ _ => rfl)
-- one message, infinitely many keys
noncomputable def unS : EncScheme Unit ℕ Unit :=
  EncScheme.ofPure (PMF.pure 0) (fun _ m => m) (fun _ c => c) (fun _ _ => rfl)
theorem idS_cd (m : Bool) : idS.ciphertextDist m = PMF.pure m := PMF.pure_bind _ _
theorem idS_nci : ¬ idS.CiphertextIndist := fun h => by
  have := congrArg (fun p : PMF Bool => p true) (h true false)
  simp [idS_cd] at this
theorem idS_nps : ¬ idS.PerfectlySecret := fun h =>
  idS_nci ((EncScheme.perfectlySecret_iff_ciphertextIndist _).mp h)
theorem unS_ps : unS.PerfectlySecret :=
  (EncScheme.perfectlySecret_iff_ciphertextIndist _).mpr fun _ _ => rfl
end

section
open Cslib.Crypto.Protocols.SecretSharing
-- one party whose share is the secret; authorized iff the party is present
noncomputable def ssI : Scheme Bool Unit Unit Bool where
  gen := PMF.pure ()
  share _ b _ := b
  reconstruct s v := if h : () ∈ s then v ⟨(), h⟩ else false
  authorized s := () ∈ s
  authorized_mono _ _ h x := h x
  correct _ _ _ h := by simp [h]
  view_indist s h _ _ := by
    simp only [viewDistOf, PMF.pure_map]; congr 1; funext i; exact absurd i.2 h
theorem ssI_vd (s : Finset Unit) (b : Bool) :
    viewDistOf ssI.gen ssI.share s b = PMF.pure (fun _ => b) := PMF.pure_map _ _
theorem ssI_ne : viewDistOf ssI.gen ssI.share {()} true ≠ viewDistOf ssI.gen ssI.share {()} false := by
  rw [ssI_vd, ssI_vd]; intro h
  have h2 := congrArg PMF.support h
  simp only [PMF.support_pure, Set.singleton_eq_singleton_iff] at h2
  have := congrFun h2 ⟨(), by simp⟩; simp at this
end

section
open Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial Polynomial
-- reconstruction from two equal nodes gives 0 (every Lagrange basis polynomial vanishes)
theorem recConst (σ : Fin 2 → ℚ) : reconstruct (fun _ : Fin 2 => (0 : ℚ)) σ = 0 := by
  classical
  simp [reconstruct, Lagrange.interpolate_apply, Lagrange.basis, Lagrange.basisDivisor_self]
-- reconstruction from one node returns the value there
theorem recOne (σ : Unit → ℚ) : reconstruct (fun _ : Unit => (1 : ℚ)) σ = σ () := by
  classical
  simp [reconstruct, Finset.univ_unique]
end

section
open Cslib.Crypto.Protocols.SecretSharing Cslib.Crypto.Protocols.SecretSharing.Shamir
-- one party at point 1, threshold 0
def pQ : Params ℚ Unit := ⟨0, by simp, fun _ => 1, fun _ _ _ => rfl, fun _ => one_ne_zero⟩
noncomputable def tsQ : TailSampler pQ where
  gen := PMF.pure 0
  map_add_eq_self δ := by
    rw [PMF.pure_map]; congr 1; funext i; exact i.elim0
theorem shQ (c : Randomness pQ) (a b : ℚ) : share pQ c a () - share pQ c b () = a - b := by
  simp [share, pQ]
end

section
-- sequences as in good_selections_exist: v is injective
theorem gsInj {V : Type} (vs : ℕ → Set V) (v : ℕ → V)
    (h : ∀ n, v n ∈ (⋂ m < n, vs m) \ vs n) : Function.Injective v := by
  have key : ∀ m n, m < n → v m ≠ v n := by
    intro m n hmn he
    have h1 := (h n).1; simp only [Set.mem_iInter] at h1
    exact (h m).2 (he ▸ h1 m hmn)
  intro a b hab
  rcases lt_trichotomy a b with h' | h' | h'
  · exact absurd hab (key a b h')
  · exact h'
  · exact absurd hab.symm (key b a h')
end

section
-- bind-counting monad (not lawful), from W1c0
@[instance_reducible] def cntM : Monad (fun α => ℕ × α) where
  pure a := (0, a)
  bind x f := ((f x.2).1 + x.1 + 1, (f x.2).2)
-- the identity signature and its counting interpreter
abbrev FI : Type → Type := fun ι => ι
def cI {ι : Type} (x : FI ι) : ℕ × ι := (0, x)
def isLB {F : Type → Type} {α : Type} : Cslib.FreeM F α → Prop
  | .pure _ => False
  | .liftBind _ _ => True
def isP {F : Type → Type} {α : Type} : Cslib.FreeM F α → Prop
  | .pure _ => True
  | .liftBind _ _ => False
end

end W3c1

section
open W3c1 Cslib.Crypto.PRG Cslib.Crypto.PRG.Generator

-- `Cslib.Crypto.PRG.Generator.advantage_nonneg` idx 3: necessary (Seed = Empty)
theorem an3 : ¬ indep0% Cslib.Crypto.PRG.Generator.advantage_nonneg 3 := fun h =>
  (@h Empty Unit _ _ ⟨()⟩ gE advT).elim (fun e => nomatch e)

-- `Cslib.Crypto.PRG.Generator.advantage_le_one` idx 3: necessary (Seed = Empty)
theorem al3 : ¬ indep0% Cslib.Crypto.PRG.Generator.advantage_le_one 3 := fun h =>
  (@h Empty Unit _ _ ⟨()⟩ gE advT).elim (fun e => nomatch e)

-- `Cslib.Crypto.PRG.Generator.secure_one` idx 3: necessary (Seed = Empty)
theorem so3 : ¬ indep0% Cslib.Crypto.PRG.Generator.secure_one 3 := fun h =>
  (@h Empty Unit _ _ ⟨()⟩ gE (fun _ => True)).elim (fun e => nomatch e)

-- `Cslib.Crypto.PRG.Generator.advantage_const` idx 3: necessary (Seed = Empty)
theorem ac3 : ¬ indep0% Cslib.Crypto.PRG.Generator.advantage_const 3 := fun h =>
  (@h Empty Unit _ _ ⟨()⟩ gE (PMF.pure true)).elim (fun e => nomatch e)

-- `Cslib.Crypto.PRG.Generator.secure_zero_of_outputDist_eq` idx 3: necessary (Seed = Empty)
theorem sz3 : ¬ indep0% Cslib.Crypto.PRG.Generator.secure_zero_of_outputDist_eq 3 := fun h =>
  (@h Empty Unit _ _ ⟨()⟩ gE (fun _ => True)).elim (fun e => nomatch e)

-- `Cslib.Crypto.PRG.Generator.secure_zero_iff_outputDist_eq_uniform` idx 3: necessary (Seed = Empty)
theorem szi3 : ¬ indep0% Cslib.Crypto.PRG.Generator.secure_zero_iff_outputDist_eq_uniform 3 := fun h =>
  (@h Empty Unit _ _ ⟨()⟩ gE).elim (fun e => nomatch e)

-- `Cslib.Crypto.PRG.Generator.Secure.mono` idx 3: necessary (Seed = Empty)
theorem mo3 : ¬ indep0% Cslib.Crypto.PRG.Generator.Secure.mono 3 := fun h =>
  (@h Empty Unit _ _ ⟨()⟩ gE (fun _ => True)).elim (fun e => nomatch e)

-- `Cslib.Crypto.PRG.Generator.Secure.of_admissible` idx 3: necessary (Seed = Empty)
theorem oa3 : ¬ indep0% Cslib.Crypto.PRG.Generator.Secure.of_admissible 3 := fun h =>
  (@h Empty Unit _ _ ⟨()⟩ gE (fun _ => True) (fun _ => True) 0 (fun _ x => x)).elim (fun e => nomatch e)

-- `Cslib.Crypto.PRG.Generator.realExperiment_rangeAdversary` idx 3: necessary (Seed = Empty)
theorem rr3 : ¬ indep0% Cslib.Crypto.PRG.Generator.realExperiment_rangeAdversary 3 := fun h =>
  (@h Empty Unit _ _ gE).elim (fun e => nomatch e)

-- `Cslib.Crypto.PRG.Generator.idealExperiment_rangeAdversary` idx 4: necessary (Seed = Output = Empty)
theorem ir4 : ¬ indep0% Cslib.Crypto.PRG.Generator.idealExperiment_rangeAdversary 4 := fun h =>
  (@h Empty Empty _ _ _ ⟨id⟩).elim (fun e => nomatch e)

-- `Cslib.Crypto.PRG.Generator.advantage_rangeAdversary` idx 3: necessary (Seed = Empty)
theorem ar3 : ¬ indep0% Cslib.Crypto.PRG.Generator.advantage_rangeAdversary 3 := fun h =>
  (@h Empty Unit _ _ ⟨()⟩ _ gE).elim (fun e => nomatch e)

-- `Cslib.Crypto.PRG.Generator.one_sub_card_div_le_advantage_rangeAdversary` idx 3: necessary (Seed = Empty)
theorem os3 : ¬ indep0% Cslib.Crypto.PRG.Generator.one_sub_card_div_le_advantage_rangeAdversary 3 := fun h =>
  (@h Empty Unit _ _ ⟨()⟩ _ gE).elim (fun e => nomatch e)

-- `Cslib.Crypto.PRG.Generator.not_secure_of_rangeAdversary` idx 3: necessary (Seed = Empty)
theorem nsr3 : ¬ indep0% Cslib.Crypto.PRG.Generator.not_secure_of_rangeAdversary 3 := fun h =>
  (@h Empty Unit _ _ ⟨()⟩ _ gE (fun _ => True) 0 trivial (by simp)).elim (fun e => nomatch e)

-- `Cslib.Crypto.PRG.Generator.not_secure_zero_of_isExpanding` idx 3: necessary (Seed = Empty)
theorem nse3 : ¬ indep0% Cslib.Crypto.PRG.Generator.not_secure_zero_of_isExpanding 3 := fun h =>
  (@h Empty Unit _ _ ⟨()⟩ gE (by simp [IsExpanding])).elim (fun e => nomatch e)

-- `Cslib.Crypto.PRG.Generator.not_exists_isExpanding_secure_zero` idx 3: necessary (Seed = Empty)
theorem ne3 : ¬ indep0% Cslib.Crypto.PRG.Generator.not_exists_isExpanding_secure_zero 3 := fun h =>
  (@h Empty Unit _ _ ⟨()⟩).elim (fun e => nomatch e)

-- `Cslib.Crypto.PRG.Generator.not_exists_isExpanding_secure_zero` idx 5: necessary (Seed = Unit, Output = Empty)
theorem ne5 : ¬ indep0% Cslib.Crypto.PRG.Generator.not_exists_isExpanding_secure_zero 5 := fun h =>
  (@h Unit Empty _ ⟨()⟩ _).elim (fun e => nomatch e)

-- `Cslib.Crypto.PRG.Generator.outputDist_prod` idx 3: necessary (Seed = Empty)
theorem op3 : ¬ indep0% Cslib.Crypto.PRG.Generator.outputDist_prod 3 := fun h =>
  (@h Empty Unit _ gE).elim (fun e => nomatch e)

-- `Cslib.Crypto.PRG.Generator.realExperiment_prod` idx 3: necessary (Seed = Empty)
theorem rp3 : ¬ indep0% Cslib.Crypto.PRG.Generator.realExperiment_prod 3 := fun h =>
  (@h Empty Unit _ gE advT).elim (fun e => nomatch e)

-- `Cslib.Crypto.PRG.Generator.idealExperiment_rightReduction` idx 2: necessary (Output = Empty)
theorem irr2 : ¬ indep0% Cslib.Crypto.PRG.Generator.idealExperiment_rightReduction 2 := fun h =>
  (@h Empty _ advT).elim (fun e => nomatch e)

-- `Cslib.Crypto.PRG.Generator.advantage_prod_le` idx 3: necessary (Seed = Empty)
theorem ap3 : ¬ indep0% Cslib.Crypto.PRG.Generator.advantage_prod_le 3 := fun h =>
  (@h Empty Unit _ _ ⟨()⟩ gE advT).elim (fun e => nomatch e)

-- `Cslib.Crypto.PRG.Generator.Secure.prod` idx 3: necessary (Seed = Empty)
theorem pr3 : ¬ indep0% Cslib.Crypto.PRG.Generator.Secure.prod 3 := fun h =>
  (@h Empty Unit _ _ ⟨()⟩ gE (fun _ => True) (fun _ => True) 0 (fun _ _ => trivial)).elim (fun e => nomatch e)

-- `Cslib.Crypto.PRG.Generator.advantage_nonneg` idx 5: removable (Nonempty Output follows from Nonempty Seed and G)
theorem rmO0 : indep% Cslib.Crypto.PRG.Generator.advantage_nonneg 5 := by
  intros; rcases ‹Nonempty _› with ⟨s⟩; exact ⟨‹Generator _ _› s⟩

-- `Cslib.Crypto.PRG.Generator.advantage_le_one` idx 5: removable (Nonempty Output follows from Nonempty Seed and G)
theorem rmO1 : indep% Cslib.Crypto.PRG.Generator.advantage_le_one 5 := by
  intros; rcases ‹Nonempty _› with ⟨s⟩; exact ⟨‹Generator _ _› s⟩

-- `Cslib.Crypto.PRG.Generator.secure_one` idx 5: removable (Nonempty Output follows from Nonempty Seed and G)
theorem rmO2 : indep% Cslib.Crypto.PRG.Generator.secure_one 5 := by
  intros; rcases ‹Nonempty _› with ⟨s⟩; exact ⟨‹Generator _ _› s⟩

-- `Cslib.Crypto.PRG.Generator.advantage_const` idx 5: removable (Nonempty Output follows from Nonempty Seed and G)
theorem rmO3 : indep% Cslib.Crypto.PRG.Generator.advantage_const 5 := by
  intros; rcases ‹Nonempty _› with ⟨s⟩; exact ⟨‹Generator _ _› s⟩

-- `Cslib.Crypto.PRG.Generator.secure_zero_of_outputDist_eq` idx 5: removable (Nonempty Output follows from Nonempty Seed and G)
theorem rmO4 : indep% Cslib.Crypto.PRG.Generator.secure_zero_of_outputDist_eq 5 := by
  intros; rcases ‹Nonempty _› with ⟨s⟩; exact ⟨‹Generator _ _› s⟩

-- `Cslib.Crypto.PRG.Generator.secure_zero_iff_outputDist_eq_uniform` idx 5: removable (Nonempty Output follows from Nonempty Seed and G)
theorem rmO5 : indep% Cslib.Crypto.PRG.Generator.secure_zero_iff_outputDist_eq_uniform 5 := by
  intros; rcases ‹Nonempty _› with ⟨s⟩; exact ⟨‹Generator _ _› s⟩

-- `Cslib.Crypto.PRG.Generator.Secure.mono` idx 5: removable (Nonempty Output follows from Nonempty Seed and G)
theorem rmO6 : indep% Cslib.Crypto.PRG.Generator.Secure.mono 5 := by
  intros; rcases ‹Nonempty _› with ⟨s⟩; exact ⟨‹Generator _ _› s⟩

-- `Cslib.Crypto.PRG.Generator.Secure.of_admissible` idx 5: removable (Nonempty Output follows from Nonempty Seed and G)
theorem rmO7 : indep% Cslib.Crypto.PRG.Generator.Secure.of_admissible 5 := by
  intros; rcases ‹Nonempty _› with ⟨s⟩; exact ⟨‹Generator _ _› s⟩

-- `Cslib.Crypto.PRG.Generator.advantage_rangeAdversary` idx 5: removable (Nonempty Output follows from Nonempty Seed and G)
theorem rmO8 : indep% Cslib.Crypto.PRG.Generator.advantage_rangeAdversary 5 := by
  intros; rcases ‹Nonempty _› with ⟨s⟩; exact ⟨‹Generator _ _› s⟩

-- `Cslib.Crypto.PRG.Generator.one_sub_card_div_le_advantage_rangeAdversary` idx 5: removable (Nonempty Output follows from Nonempty Seed and G)
theorem rmO9 : indep% Cslib.Crypto.PRG.Generator.one_sub_card_div_le_advantage_rangeAdversary 5 := by
  intros; rcases ‹Nonempty _› with ⟨s⟩; exact ⟨‹Generator _ _› s⟩

-- `Cslib.Crypto.PRG.Generator.not_secure_of_rangeAdversary` idx 5: removable (Nonempty Output follows from Nonempty Seed and G)
theorem rmO10 : indep% Cslib.Crypto.PRG.Generator.not_secure_of_rangeAdversary 5 := by
  intros; rcases ‹Nonempty _› with ⟨s⟩; exact ⟨‹Generator _ _› s⟩

-- `Cslib.Crypto.PRG.Generator.not_secure_zero_of_isExpanding` idx 5: removable (Nonempty Output follows from Nonempty Seed and G)
theorem rmO11 : indep% Cslib.Crypto.PRG.Generator.not_secure_zero_of_isExpanding 5 := by
  intros; rcases ‹Nonempty _› with ⟨s⟩; exact ⟨‹Generator _ _› s⟩

-- `Cslib.Crypto.PRG.Generator.idealExperiment_leftReduction` idx 5: removable (Nonempty Output follows from Nonempty Seed and G)
theorem rmO12 : indep% Cslib.Crypto.PRG.Generator.idealExperiment_leftReduction 5 := by
  intros; rcases ‹Nonempty _› with ⟨s⟩; exact ⟨‹Generator _ _› s⟩

-- `Cslib.Crypto.PRG.Generator.advantage_prod_le` idx 5: removable (Nonempty Output follows from Nonempty Seed and G)
theorem rmO13 : indep% Cslib.Crypto.PRG.Generator.advantage_prod_le 5 := by
  intros; rcases ‹Nonempty _› with ⟨s⟩; exact ⟨‹Generator _ _› s⟩

-- `Cslib.Crypto.PRG.Generator.Secure.prod` idx 5: removable (Nonempty Output follows from Nonempty Seed and G)
theorem rmO14 : indep% Cslib.Crypto.PRG.Generator.Secure.prod 5 := by
  intros; rcases ‹Nonempty _› with ⟨s⟩; exact ⟨‹Generator _ _› s⟩
end

section
open W3c1 Cslib.Crypto.PRG Cslib.Crypto.PRG.Generator
-- `Cslib.Crypto.PRG.Generator.secure_zero_of_outputDist_eq` idx 7: necessary (gT : Unit → Bool is expanding)
theorem sz7 : ¬ drop0% Cslib.Crypto.PRG.Generator.secure_zero_of_outputDist_eq 7 := fun h =>
  gT_ns (@h _ _ _ _ _ _ gT (fun _ => True))
-- `Cslib.Crypto.PRG.Generator.Secure.of_admissible` idx 10: necessary (gT, everything admissible, ε = 0)
theorem oa10 : ¬ drop0% Cslib.Crypto.PRG.Generator.Secure.of_admissible 10 := fun h =>
  gT_ns (@h _ _ _ _ _ _ gT (fun _ => True) (fun _ => True) 0 (fun _ x => x))
-- `Cslib.Crypto.PRG.Generator.Secure.of_admissible` idx 11: necessary (nothing admissible, everything restricted)
theorem oa11 : ¬ drop0% Cslib.Crypto.PRG.Generator.Secure.of_admissible 11 := fun h =>
  gT_ns (@h _ _ _ _ _ _ gT (fun _ => False) (fun _ => True) 0 (fun _ x => x.elim))
-- `Cslib.Crypto.PRG.Generator.not_secure_of_rangeAdversary` idx 10: necessary (nothing admissible: trivially secure)
theorem nsr10 : ¬ drop0% Cslib.Crypto.PRG.Generator.not_secure_of_rangeAdversary 10 := fun h =>
  @h _ _ _ _ _ _ _ gT (fun _ => False) 0 (by norm_num) (fun _ x => x.elim)
-- `Cslib.Crypto.PRG.Generator.not_secure_of_rangeAdversary` idx 11: necessary (ε = 1, secure_one)
theorem nsr11 : ¬ drop0% Cslib.Crypto.PRG.Generator.not_secure_of_rangeAdversary 11 := fun h =>
  @h _ _ _ _ _ _ _ gT (fun _ => True) 1 trivial (secure_one _ _)
-- `Cslib.Crypto.PRG.Generator.not_secure_zero_of_isExpanding` idx 7: necessary (identity generator on Unit has uniform output)
theorem nse7 : ¬ drop0% Cslib.Crypto.PRG.Generator.not_secure_zero_of_isExpanding 7 := fun h =>
  @h _ _ _ _ _ _ gU (secure_zero_of_outputDist_eq _ (by simp [outputDist, gU]; exact PMF.map_id _) _)
end

section
open W3c1 Cslib.Crypto.PRG Cslib.Crypto.PRG.Generator

-- `Cslib.Crypto.PRG.Generator.Secure.prod` idx 10: necessary (gT.prod is expanding, ε = 0)
theorem pr10 : ¬ drop0% Cslib.Crypto.PRG.Generator.Secure.prod 10 := fun h =>
  not_secure_zero_of_isExpanding gT.prod (by simp [IsExpanding])
    (by simpa using @h _ _ _ _ _ _ gT (fun _ => True) (fun _ => True) 0 (fun _ _ => trivial) (fun _ _ => trivial))
open W3c1

-- `Cslib.Crypto.PRG.Generator.Secure.prod` idx 11: necessary (only A(y₁,y₂) = rangeTest y₁ admissible; its right reduction is constant)
theorem pr11 : ¬ drop0% Cslib.Crypto.PRG.Generator.Secure.prod 11 := fun h => by
  have := @h _ _ _ _ _ _ gT (fun B => B = rightReduction A1) (fun A => A = A1) 0
    (fun a ha => ha ▸ rA1) (fun A hA => hA ▸ rfl) A1 rfl
  rw [show gT.prod.advantage A1 = _ from advFst gT gT.rangeAdversary] at this; have := gT_rng; simp at *; linarith
-- `Cslib.Crypto.PRG.Generator.Secure.prod` idx 12: necessary (only A(y₁,y₂) = rangeTest y₂ admissible; its left reduction is constant)
theorem pr12 : ¬ drop0% Cslib.Crypto.PRG.Generator.Secure.prod 12 := fun h => by
  have := @h _ _ _ _ _ _ gT (fun B => B = gT.leftReduction A2) (fun A => A = A2) 0
    (fun a ha => ha ▸ lA2) (fun A hA => hA ▸ rfl) A2 rfl
  rw [show gT.prod.advantage A2 = _ from advSnd gT gT.rangeAdversary] at this; have := gT_rng; simp at *; linarith
end

section
open W3c1 Cslib.Crypto.Protocols.Commitment Cslib.Crypto.Protocols.Commitment.Scheme Cslib.Probability.PMF

-- `Cslib.Crypto.Protocols.Commitment.Scheme.PerfectlyBinding.disjoint_support_commitmentDist` idx 4: necessary (sc0: constant commitment)
theorem cd4 : ¬ drop0% Cslib.Crypto.Protocols.Commitment.Scheme.PerfectlyBinding.disjoint_support_commitmentDist 4 :=
  fun h => by
    have hd := @h _ _ _ sc0 true false (by decide)
    rw [Set.disjoint_left] at hd
    exact hd (a := ()) (by simp [commitmentDist, sc0]) (by simp [commitmentDist, sc0])
-- `Cslib.Crypto.Protocols.Commitment.Scheme.PerfectlyBinding.disjoint_support_commitmentDist` idx 7: necessary (scB, equal messages)
theorem cd7 : ¬ drop0% Cslib.Crypto.Protocols.Commitment.Scheme.PerfectlyBinding.disjoint_support_commitmentDist 7 :=
  fun h => by
    have hd := @h _ _ _ scB scB_bind true true
    rw [Set.disjoint_left] at hd
    exact hd (a := true) (by simp [commitmentDist, scB]) (by simp [commitmentDist, scB])
-- `Cslib.Crypto.Protocols.Commitment.Scheme.PerfectlyBinding.dist_commitmentDist_eq_one` idx 5: necessary (sc0: equal distributions)
theorem de5 : ¬ drop0% Cslib.Crypto.Protocols.Commitment.Scheme.PerfectlyBinding.dist_commitmentDist_eq_one 5 :=
  fun h => by
    have := @h _ _ _ _ sc0 true false (by decide)
    rw [show sc0.commitmentDist true = sc0.commitmentDist false from rfl, dist_self] at this
    exact zero_ne_one this
-- `Cslib.Crypto.Protocols.Commitment.Scheme.PerfectlyBinding.dist_commitmentDist_eq_one` idx 8: necessary (scB, equal messages)
theorem de8 : ¬ drop0% Cslib.Crypto.Protocols.Commitment.Scheme.PerfectlyBinding.dist_commitmentDist_eq_one 8 :=
  fun h => by
    have := @h _ _ _ _ scB scB_bind true true
    rw [dist_self] at this
    exact zero_ne_one this
-- `Cslib.Crypto.Protocols.Commitment.Scheme.subsingleton_of_statisticallyHiding_of_perfectlyBinding` idx 6: necessary (scB, ε = 1)
theorem ss6 : ¬ drop0% Cslib.Crypto.Protocols.Commitment.Scheme.subsingleton_of_statisticallyHiding_of_perfectlyBinding 6 :=
  fun h => by
    have hh : scB.StatisticallyHiding 1 := fun _ _ => by
      unfold StatisticallyClose; rw [NNReal.coe_one]; exact Cslib.Probability.PMF.dist_le_one _ _
    exact bool_nss (@h _ _ _ _ scB 1 hh scB_bind)
-- `Cslib.Crypto.Protocols.Commitment.Scheme.subsingleton_of_statisticallyHiding_of_perfectlyBinding` idx 7: necessary (scB, ε = 0)
theorem ss7 : ¬ drop0% Cslib.Crypto.Protocols.Commitment.Scheme.subsingleton_of_statisticallyHiding_of_perfectlyBinding 7 :=
  fun h => bool_nss (@h _ _ _ _ scB 0 (by norm_num) scB_bind)
-- `Cslib.Crypto.Protocols.Commitment.Scheme.subsingleton_of_statisticallyHiding_of_perfectlyBinding` idx 8: necessary (sc0, ε = 0)
theorem ss8 : ¬ drop0% Cslib.Crypto.Protocols.Commitment.Scheme.subsingleton_of_statisticallyHiding_of_perfectlyBinding 8 :=
  fun h => bool_nss (@h _ _ _ _ sc0 0 (by norm_num) ((perfectlyHiding_iff_statisticallyHiding_zero sc0).mp sc0_hide))
-- `Cslib.Crypto.Protocols.Commitment.Scheme.subsingleton_of_perfectlyHiding_of_perfectlyBinding` idx 4: necessary (scB)
theorem sp4 : ¬ drop0% Cslib.Crypto.Protocols.Commitment.Scheme.subsingleton_of_perfectlyHiding_of_perfectlyBinding 4 :=
  fun h => bool_nss (@h _ _ _ scB scB_bind)
-- `Cslib.Crypto.Protocols.Commitment.Scheme.subsingleton_of_perfectlyHiding_of_perfectlyBinding` idx 5: necessary (sc0)
theorem sp5 : ¬ drop0% Cslib.Crypto.Protocols.Commitment.Scheme.subsingleton_of_perfectlyHiding_of_perfectlyBinding 5 :=
  fun h => bool_nss (@h _ _ _ sc0 sc0_hide)
-- `Cslib.Crypto.Protocols.Commitment.Scheme.correct` idx 7: necessary (scT rejects commitment false)
theorem cc7 : ¬ drop0% Cslib.Crypto.Protocols.Commitment.Scheme.correct 7 :=
  fun h => absurd (@h _ _ _ scT () false ()) (by simp [scT])
-- `Cslib.Crypto.Protocols.Commitment.Scheme.accepts_of_mem_support` idx 7: necessary (scT rejects commitment false)
theorem am7 : ¬ drop0% Cslib.Crypto.Protocols.Commitment.Scheme.accepts_of_mem_support 7 :=
  fun h => absurd (@h _ _ _ scT () false ()) (by simp [Scheme.Accepts, scT])
end

section
open W3c1 Cslib.Crypto.Protocols.PerfectSecrecy EncScheme

-- `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.indep_of_ciphertextIndist` idx 4: necessary (identity encryption is not perfectly secret)
theorem ic4 : ¬ drop0% Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.indep_of_ciphertextIndist 4 :=
  fun h => idS_nps ((perfectlySecret_iff_indep idS).mpr (@h _ _ _ idS))
-- `_private.Cslib.Crypto.Protocols.PerfectSecrecy.Basic.0.Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.encrypt_key_injective` idx 7: necessary (one key, two messages)
theorem eki7 : ¬ drop0% _private.Cslib.Crypto.Protocols.PerfectSecrecy.Basic.«0».Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.encrypt_key_injective 7 :=
  fun h => absurd (@h _ _ _ idS (fun _ => ()) true (fun _ => by simp [idS, EncScheme.ofPure]) (a₁ := true) (a₂ := false) rfl) (by decide)
-- `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.perfectlySecret_keySpace_ge` idx 3: necessary (K = ℕ: Nat.card ℕ = 0)
theorem pk3 : ¬ drop0% Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.perfectlySecret_keySpace_ge 3 :=
  fun h => by have := @h _ _ _ unS unS_ps; simp at this
-- `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.perfectlySecret_keySpace_ge` idx 5: necessary (identity encryption, 2 messages, 1 key)
theorem pk5 : ¬ drop0% Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.perfectlySecret_keySpace_ge 5 :=
  fun h => by have := @h _ _ _ _ idS; simp at this
-- `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.posteriorMsgDist_apply` idx 6: necessary (prior pure true, ciphertext false)
theorem pm6 : ¬ indep0% Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.posteriorMsgDist_apply 6 :=
  fun h => by
    have := @h _ _ _ idS (PMF.pure true) false true
    have e : idS.marginalCiphertextDist (PMF.pure true) = PMF.pure true :=
      (PMF.pure_bind _ _).trans (idS_cd true)
    rw [e] at this; simp at this
-- `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.correct` idx 8: necessary (identity decryption of a foreign ciphertext)
theorem ec8 : ¬ drop0% Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.correct 8 :=
  fun h => absurd (@h _ _ _ idS () (by simp [idS, EncScheme.ofPure]) true false) (by simp [idS, EncScheme.ofPure])
end

section
open W3c1 Cslib.Crypto.Protocols.SecretSharing Scheme

-- `Cslib.Crypto.Protocols.SecretSharing.Scheme.viewDist_eq_of_not_authorized` idx 6: necessary (authorized singleton coalition sees the secret)
theorem vd6 : ¬ drop0% Cslib.Crypto.Protocols.SecretSharing.Scheme.viewDist_eq_of_not_authorized 6 :=
  fun h => ssI_ne (@h _ _ _ _ ssI {()} true false)
-- `Cslib.Crypto.Protocols.SecretSharing.Scheme.view_indist` idx 6: necessary (authorized singleton coalition sees the secret)
theorem vi6 : ¬ drop0% Cslib.Crypto.Protocols.SecretSharing.Scheme.view_indist 6 :=
  fun h => ssI_ne (@h _ _ _ _ ssI {()} true false)
-- `Cslib.Crypto.Protocols.SecretSharing.Scheme.posteriorSecretDist_apply` idx 8: necessary (prior pure true, view false)
theorem psd8 : ¬ indep0% Cslib.Crypto.Protocols.SecretSharing.Scheme.posteriorSecretDist_apply 8 :=
  fun h => by
    have := @h _ _ _ _ ssI {()} (PMF.pure true) (fun _ => false) true
    rw [PMF.pure_bind] at this
    simp only [viewDist, ssI_vd, PMF.mem_support_pure_iff] at this
    have := congrFun this ⟨(), by simp⟩; simp at this
-- `Cslib.Crypto.Protocols.SecretSharing.Scheme.correct` idx 8: necessary (empty coalition reconstructs false)
theorem sc8 : ¬ drop0% Cslib.Crypto.Protocols.SecretSharing.Scheme.correct 8 :=
  fun h => absurd (@h _ _ _ _ ssI () true ∅) (by simp [ssI])
-- `Cslib.Crypto.Protocols.SecretSharing.Scheme.reconstruct_view_eq_secret` idx 8: necessary (empty coalition reconstructs false)
theorem rv8 : ¬ drop0% Cslib.Crypto.Protocols.SecretSharing.Scheme.reconstruct_view_eq_secret 8 :=
  fun h => absurd (@h _ _ _ _ ssI () true ∅) (by simp [ssI])
end

section
open W3c1 Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial Polynomial

-- `Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.natDegree_sharingPolynomial_le` idx 5: necessary (tail = X, n = 0)
theorem nd5 : ¬ drop0% Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.natDegree_sharingPolynomial_le 5 :=
  fun h => by
    have := @h ℚ _ 0 X 0
    simp [sharingPolynomial, ← pow_two] at this
-- `Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.degree_sharingPolynomial_lt_succ` idx 5: necessary (tail = X, n = 0)
theorem ds5 : ¬ drop0% Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.degree_sharingPolynomial_lt_succ 5 :=
  fun h => by
    have := @h ℚ _ 0 X 0
    simp [sharingPolynomial, ← pow_two] at this
-- `Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.reconstruct_eq_constantCoeff_of_eval_eq` idx 6: necessary (two equal nodes, p = 1)
theorem rc6 : ¬ drop0% Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.reconstruct_eq_constantCoeff_of_eval_eq 6 :=
  fun h => by
    have := @h ℚ _ (Fin 2) _ (fun _ => 0) 1 (by simp)
    rw [recConst] at this; simp at this
-- `Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.reconstruct_eq_constantCoeff_of_eval_eq` idx 7: necessary (one node at 1, p = X)
theorem rc7 : ¬ drop0% Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.reconstruct_eq_constantCoeff_of_eval_eq 7 :=
  fun h => by
    have := @h ℚ _ Unit _ (fun _ => 1) X (fun _ _ _ => rfl)
    rw [recOne] at this; simp at this
-- `Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.reconstruct_sharingPolynomial_eq_secret` idx 7: necessary (two equal nodes, secret 1, tail 0)
theorem rs7 : ¬ drop0% Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.reconstruct_sharingPolynomial_eq_secret 7 :=
  fun h => by
    have := @h ℚ _ (Fin 2) _ (fun _ => 0) 1 0 (by simp [sharingPolynomial])
    rw [recConst] at this; simp at this
-- `Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.reconstruct_sharingPolynomial_eq_secret` idx 8: necessary (one node at 1, secret 0, tail 1)
theorem rs8 : ¬ drop0% Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.reconstruct_sharingPolynomial_eq_secret 8 :=
  fun h => by
    have := @h ℚ _ Unit _ (fun _ => 1) 0 1 (fun _ _ _ => rfl)
    rw [recOne] at this; simp [sharingPolynomial] at this
end

section
open W3c1 Cslib.Crypto.Protocols.SecretSharing Cslib.Crypto.Protocols.SecretSharing.Shamir

-- `_private.Cslib.Crypto.Protocols.SecretSharing.Shamir.0.Cslib.Crypto.Protocols.SecretSharing.Shamir.privacyCorrectionPolynomial_degree_lt` idx 8: necessary (threshold 0, coalition of 1: correction polynomial is the nonzero constant 1)
theorem pcd8 : ¬ drop0% _private.Cslib.Crypto.Protocols.SecretSharing.Shamir.«0».Cslib.Crypto.Protocols.SecretSharing.Shamir.privacyCorrectionPolynomial_degree_lt 8 :=
  fun h => by
    have hd := @h ℚ Unit _ _ pQ {()} 1 0
    have he := (priv% _private.Cslib.Crypto.Protocols.SecretSharing.Shamir.«0».Cslib.Crypto.Protocols.SecretSharing.Shamir.privacyCorrectionPolynomial_eval)
      pQ {()} (1 : ℚ) 0 ⟨(), by simp⟩
    generalize (priv% _private.Cslib.Crypto.Protocols.SecretSharing.Shamir.«0».Cslib.Crypto.Protocols.SecretSharing.Shamir.privacyCorrectionPolynomial) pQ {()} (1 : ℚ) 0 = P at hd he
    have : P = 0 := by
      by_contra hne
      exact absurd hd (not_lt.mpr (by simpa [pQ] using _root_.Polynomial.zero_le_degree_iff.mpr hne))
    subst this; simp [pQ] at he
-- `_private.Cslib.Crypto.Protocols.SecretSharing.Shamir.0.Cslib.Crypto.Protocols.SecretSharing.Shamir.tailPolynomial_privacyCorrection` idx 6: necessary (threshold 0, coalition of 1)
theorem tpc6 : ¬ indep0% _private.Cslib.Crypto.Protocols.SecretSharing.Shamir.«0».Cslib.Crypto.Protocols.SecretSharing.Shamir.tailPolynomial_privacyCorrection 6 :=
  fun h => absurd (@h ℚ Unit _ _ pQ {()}) (by simp [pQ])
-- `_private.Cslib.Crypto.Protocols.SecretSharing.Shamir.0.Cslib.Crypto.Protocols.SecretSharing.Shamir.view_eq_view_add_privacyCorrection` idx 6: necessary (threshold 0, coalition of 1)
theorem vvp6 : ¬ indep0% _private.Cslib.Crypto.Protocols.SecretSharing.Shamir.«0».Cslib.Crypto.Protocols.SecretSharing.Shamir.view_eq_view_add_privacyCorrection 6 :=
  fun h => absurd (@h ℚ Unit _ _ pQ {()}) (by simp [pQ])
-- `Cslib.Crypto.Protocols.SecretSharing.Shamir.view_indist_of_tailSampler` idx 7: necessary (authorized coalition of 1 sees the secret)
theorem vit7 : ¬ drop0% Cslib.Crypto.Protocols.SecretSharing.Shamir.view_indist_of_tailSampler 7 :=
  fun h => by
    have := @h ℚ Unit _ _ pQ tsQ {()} 1 0
    simp only [viewDistOf, tsQ, PMF.pure_map] at this
    have h2 := congrArg PMF.support this
    simp only [PMF.support_pure, Set.singleton_eq_singleton_iff] at h2
    have h3 := congrFun h2 ⟨(), by simp⟩
    have := shQ 0 1 0; simp only [h3, sub_self] at this; norm_num at this
-- `Cslib.Crypto.Protocols.SecretSharing.Shamir.scheme_authorized_iff` idx 6: removable (a field is nonempty)
theorem sai6 : indep% Cslib.Crypto.Protocols.SecretSharing.Shamir.scheme_authorized_iff 6 := by
  intros; exact ⟨0⟩
-- `Cslib.Crypto.Protocols.SecretSharing.Shamir.reconstruct_view_eq_secret` idx 9: necessary (empty coalition reconstructs 0)
theorem srv9 : ¬ drop0% Cslib.Crypto.Protocols.SecretSharing.Shamir.reconstruct_view_eq_secret 9 :=
  fun h => by
    have := @h ℚ Unit _ _ pQ tsQ 0 1 ∅
    simp [schemeWith, Shamir.reconstruct, Polynomial.reconstruct] at this
end

section
open W3c1 Cslib

-- `Cslib.infinite_pigeonhole_principle` idx 2: necessary (f = id on ℕ, s = univ)
theorem ipp2 : ¬ drop0% Cslib.infinite_pigeonhole_principle 2 := fun h => by
  obtain ⟨y, t, ht, -, hf⟩ := @h ℕ ℕ id Set.univ Set.infinite_univ
  exact ht ((Set.finite_singleton y).subset fun x hx => hf x hx)
-- `Cslib.infinite_pigeonhole_principle` idx 5: necessary (s = ∅)
theorem ipp5 : ¬ drop0% Cslib.infinite_pigeonhole_principle 5 := fun h => by
  obtain ⟨y, t, ht, hs, -⟩ := @h Unit Unit _ id ∅
  exact ht (Set.finite_empty.subset hs)
-- `_private.Cslib.Foundations.Combinatorics.InfiniteGraphRamsey.0.Cslib.goodSelection_exists` idx 2: necessary (Color = Finset ℕ, color = id)
theorem gse2 : ¬ drop0% _private.Cslib.Foundations.Combinatorics.InfiniteGraphRamsey.«0».Cslib.goodSelection_exists 2 := fun h => by
  obtain ⟨⟨⟨vs, hinf⟩, v, c⟩, -, -, h3⟩ := @h ℕ (Finset ℕ) id ((priv% _private.Cslib.Foundations.Combinatorics.InfiniteGraphRamsey.«0».Cslib.InfVSet.mk) (Set.univ : Set ℕ) Set.infinite_univ)
  refine hinf ((Finset.finite_toSet c).subset fun u hu => ?_)
  have := h3 u hu
  simp only [id] at this
  rw [← this]; simp
-- `_private.Cslib.Foundations.Combinatorics.InfiniteGraphRamsey.0.Cslib.goodSelection_seq_prop` idx 2: necessary (Color = ℕ)
theorem gsp2 : ¬ indep0% _private.Cslib.Foundations.Combinatorics.InfiniteGraphRamsey.«0».Cslib.goodSelection_seq_prop 2 :=
  fun h => @not_finite ℕ _ (@h ℕ ℕ (fun _ => 0) _ 0)
-- `_private.Cslib.Foundations.Combinatorics.InfiniteGraphRamsey.0.Cslib.goodSelection_seq_prop` idx 4: necessary (Vertex = Unit)
theorem gsp4 : ¬ indep0% _private.Cslib.Foundations.Combinatorics.InfiniteGraphRamsey.«0».Cslib.goodSelection_seq_prop 4 :=
  fun h => @not_finite Unit (@h Unit Unit _ (fun _ => ()) 0) _
-- `_private.Cslib.Foundations.Combinatorics.InfiniteGraphRamsey.0.Cslib.good_selections_exist` idx 2: necessary (Color = Finset ℕ, color = id: vs 0 would contain infinitely many v n inside c 0)
theorem gex2 : ¬ drop0% _private.Cslib.Foundations.Combinatorics.InfiniteGraphRamsey.«0».Cslib.good_selections_exist 2 := fun h => by
  obtain ⟨vs, v, c, hh⟩ := @h ℕ (Finset ℕ) id _
  have hi := gsInj vs v fun n => (hh n).2.1
  have hmem : ∀ k, v (k + 1) ∈ (c 0 : Set ℕ) := by
    intro k
    have h1 := (hh (k + 1)).2.1.1; simp only [Set.mem_iInter] at h1
    have := (hh 0).2.2 _ (h1 0 (Nat.succ_pos k))
    simp only [id] at this
    rw [← this]; simp
  exact Set.infinite_of_injective_forall_mem (fun a b e => Nat.succ_injective (hi e)) hmem (Finset.finite_toSet _)
-- `_private.Cslib.Foundations.Combinatorics.InfiniteGraphRamsey.0.Cslib.good_selections_exist` idx 4: necessary (Vertex = Unit: v would be injective)
theorem gex4 : ¬ drop0% _private.Cslib.Foundations.Combinatorics.InfiniteGraphRamsey.«0».Cslib.good_selections_exist 4 := fun h => by
  obtain ⟨vs, v, c, hh⟩ := @h Unit Unit _ (fun _ => ())
  have hi := gsInj vs v fun n => (hh n).2.1
  exact absurd (hi (Subsingleton.elim (v 0) (v 1))) (by decide)
-- `Cslib.infinite_graph_ramsey` idx 2: necessary (Color = Finset ℕ, color = id)
theorem igr2 : ¬ drop0% Cslib.infinite_graph_ramsey 2 := fun h => by
  obtain ⟨c, s, hs, hc⟩ := @h ℕ (Finset ℕ) id _
  obtain ⟨a, ha, -⟩ := hs.exists_gt 0
  obtain ⟨b, hb, hab⟩ := hs.exists_gt a
  obtain ⟨d, hd, hbd⟩ := hs.exists_gt b
  have e1 := hc {a, b} (Finset.card_pair (by omega)) (by simp [Set.insert_subset_iff, ha, hb])
  have e2 := hc {a, d} (Finset.card_pair (by omega)) (by simp [Set.insert_subset_iff, ha, hd])
  have : d ∈ ({a, b} : Finset ℕ) := by simp only [id] at e1 e2; rw [e1, ← e2]; simp
  simp at this; omega
-- `Cslib.infinite_graph_ramsey` idx 4: necessary (Vertex = Unit has no infinite set)
theorem igr4 : ¬ drop0% Cslib.infinite_graph_ramsey 4 := fun h => by
  obtain ⟨c, s, hs, -⟩ := @h Unit Unit _ (fun _ => ())
  exact hs (Set.toFinite s)
end

section
open W3c1 Cslib

-- `Cslib.FreeM.induction` idx 3: necessary (motive "is a liftBind" fails at pure ())
theorem fi3 : ¬ drop0% Cslib.FreeM.induction 3 := fun h =>
  @h FI Unit isLB (fun _ _ _ => trivial) (.pure ())
-- `Cslib.FreeM.induction` idx 4: necessary (motive "is pure" fails at lift ())
theorem fi4 : ¬ drop0% Cslib.FreeM.induction 4 := fun h =>
  @h FI Unit isP (fun _ => trivial) (FreeM.lift (F := FI) ())
-- `Cslib.FreeM.liftM_lift` idx 4: necessary (bind-counting monad cntM)
theorem fll4 : ¬ drop0% Cslib.FreeM.liftM_lift 4 := fun h => by
  have := congrArg Prod.fst (@h FI _ cntM Unit cI ())
  exact absurd this (by decide)
-- `Cslib.FreeM.liftM_bind` idx 5: necessary (bind-counting monad cntM)
theorem flb5 : ¬ drop0% Cslib.FreeM.liftM_bind 5 := fun h => by
  have := congrArg Prod.fst (@h FI _ cntM Unit Unit cI (.pure ()) (fun _ => .pure ()))
  exact absurd this (by decide)
-- `Cslib.IsMonadHom.map_freeMLiftM` idx 7: necessary (f = fun _ => none on Option)
theorem mfl7 : ¬ drop0% Cslib.IsMonadHom.map_freeMLiftM 7 := fun h => by
  have := @h FI Option _ Unit Option _ (fun _ => none) (fun x => some x) (.pure ())
  simp [FreeM.liftM] at this
-- `Cslib.FreeM.isMonadHom_liftM` idx 3: necessary (bind-counting monad cntM breaks map_bind)
theorem iml3 : ¬ drop0% Cslib.FreeM.isMonadHom_liftM 3 := fun h => by
  have := congrArg Prod.fst (@IsMonadHom.map_bind (FreeM FI) (fun α => ℕ × α) _ cntM _ (@h FI _ cntM cI) Unit Unit (.pure ()) (fun _ => .pure ()))
  exact absurd this (by decide)
-- `Cslib.FreeM.liftM_map` idx 5: necessary (bind-counting monad cntM)
theorem flm5 : ¬ drop0% Cslib.FreeM.liftM_map 5 := fun h => by
  have := congrArg Prod.fst (@h FI _ cntM Unit Unit cI id (.pure ()))
  exact absurd this (by decide)
-- `Cslib.FreeM.liftM_seq` idx 5: necessary (bind-counting monad cntM)
theorem fls5 : ¬ drop0% Cslib.FreeM.liftM_seq 5 := fun h => by
  have := congrArg Prod.fst (@h FI _ cntM Unit Unit cI (.pure id) (.pure ()))
  exact absurd this (by decide)
-- `Cslib.FreeM.liftM_seqLeft` idx 5: necessary (bind-counting monad cntM)
theorem flsl5 : ¬ drop0% Cslib.FreeM.liftM_seqLeft 5 := fun h => by
  have := congrArg Prod.fst (@h FI _ cntM Unit Unit cI (.pure ()) (.pure ()))
  exact absurd this (by decide)
-- `Cslib.FreeM.liftM_seqRight` idx 5: necessary (bind-counting monad cntM)
theorem flsr5 : ¬ drop0% Cslib.FreeM.liftM_seqRight 5 := fun h => by
  have := congrArg Prod.fst (@h FI _ cntM Unit Unit cI (.pure ()) (.pure ()))
  exact absurd this (by decide)
-- `Cslib.FreeM.Interprets.apply_pure` idx 6: necessary (interp = fun _ => none on Option)
theorem iap6 : ¬ drop0% Cslib.FreeM.Interprets.apply_pure 6 := fun h => by
  have := @h FI Option _ Unit (fun x => some x) (fun _ => none) ()
  simp at this
-- `Cslib.FreeM.Interprets.apply_lift_bind` idx 6: necessary (handler = none, interp = some ())
theorem ialb6 : ¬ drop0% Cslib.FreeM.Interprets.apply_lift_bind 6 := fun h => by
  have := @h FI Option _ Unit (fun _ => none) (fun _ => some ()) Unit () (fun _ => .pure ())
  simp at this
-- `Cslib.FreeM.Interprets.eq` idx 6: necessary (interp = fun _ => none on Option)
theorem ieq6 : ¬ drop0% Cslib.FreeM.Interprets.eq 6 := fun h => by
  have := congrFun (@h FI Option _ Unit (fun x => some x) (fun _ => none)) (.pure ())
  simp [FreeM.liftM] at this
-- `Cslib.FreeM.liftM_comp` idx 3: necessary (bind-counting monad cntM, x = lift ())
theorem flc3 : ¬ drop0% Cslib.FreeM.liftM_comp 3 := fun h => by
  have := congrArg Prod.fst (@h FI _ cntM FI Unit (FreeM.lift (F := FI) ()) (fun x => FreeM.lift x) cI)
  exact absurd this (by decide)
-- `Cslib.FreeM.FreeState.toStateM_unique` idx 3: necessary (constant interpreter)
theorem tsu3 : ¬ drop0% Cslib.FreeM.FreeState.toStateM_unique 3 := fun h => by
  have := congrArg (fun g => (g (.pure true) ()).1) (@h Unit Bool (fun _ _ => (false, ())))
  exact absurd this (by decide)
-- `Cslib.FreeM.FreeWriter.toWriterT_unique` idx 4: necessary (constant interpreter)
theorem twu4 : ¬ drop0% Cslib.FreeM.FreeWriter.toWriterT_unique 4 := fun h => by
  have := congrArg (fun g => (g (.pure true)).1) (@h Unit Bool _ (fun _ => (false, ())))
  exact absurd this (by decide)
-- `Cslib.FreeM.FreeCont.toContT_unique` idx 3: necessary (constant interpreter)
theorem tcu3 : ¬ drop0% Cslib.FreeM.FreeCont.toContT_unique 3 := fun h => by
  have := congrArg (fun g => g (.pure true) id) (@h Bool Bool (fun _ _ => false))
  exact Bool.false_ne_true this
-- `Cslib.FreeM.FreeReader.toReaderM_unique` idx 3: necessary (constant interpreter)
theorem tru3 : ¬ drop0% Cslib.FreeM.FreeReader.toReaderM_unique 3 := fun h => by
  have := congrArg (fun g => g (.pure true) ()) (@h Unit Bool (fun _ _ => false))
  exact Bool.false_ne_true this
-- `Cslib.FreeM.foldFreeM_unique` idx 6: necessary (h = false everywhere, onValue = true)
theorem ffu6 : ¬ drop0% Cslib.FreeM.foldFreeM_unique 6 := fun h => by
  have := congrFun (@h FI Unit Bool (fun _ => true) (fun _ _ => false) (fun _ => false) (fun _ _ => rfl)) (.pure ())
  simp [FreeM.foldFreeM] at this
-- `Cslib.FreeM.foldFreeM_unique` idx 7: necessary (h = true everywhere, onEffect = false)
theorem ffu7 : ¬ drop0% Cslib.FreeM.foldFreeM_unique 7 := fun h => by
  have := congrFun (@h FI Unit Bool (fun _ => true) (fun _ _ => false) (fun _ => true) (fun _ => rfl)) (FreeM.lift (F := FI) ())
  exact absurd this (by decide)
end
