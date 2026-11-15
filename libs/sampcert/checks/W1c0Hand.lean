import Lean.Elab.Command
import SampCert
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

open SLang ENNReal

namespace W1c0
open SLang

/-- constant mechanisms -/
def Cst {T Z : Type} (m : Mechanism T Z) : Prop := ∀ l l', m l = m l'

/-- DP system: constant mechanisms at every level, everything at level at least 1 -/
noncomputable def sys (T : Type) : DPSystem T where
  prop m ε := Cst m ∨ 1 ≤ ε
  of_app_dp δ _ := if 0 < δ then 0 else 1
  prop_adp := by
    intro Z _ m δ hδ ε' h
    simp only [hδ, ite_true] at h
    rcases h with h | h
    · intro l₁ l₂ _ S
      rw [h l₁ l₂]
      have h1 : (1 : ENNReal) ≤ ENNReal.ofReal (Real.exp ε') :=
        ENNReal.one_le_ofReal.mpr (Real.one_le_exp ε'.2)
      exact le_add_left (le_mul_of_one_le_left (by simp) h1)
    · exact absurd h (by norm_num)
  prop_mono := by
    intro Z m ε₁ ε₂ hle h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hle)
  adaptive_compose_prop := by
    intro U V _ _ m₁ m₂ ε₁ ε₂ ε h1 h2 he
    by_cases hb : 1 ≤ ε
    · exact Or.inr hb
    have hb1 : ¬ 1 ≤ ε₁ := fun h => hb (he ▸ le_add_right h)
    have hb2 : ¬ 1 ≤ ε₂ := fun h => hb (he ▸ le_add_left h)
    have c1 : Cst m₁ := h1.resolve_right hb1
    have c2 : ∀ u, Cst (m₂ u) := fun u => (h2 u).resolve_right hb2
    left
    intro l l'
    unfold privComposeAdaptive
    rw [c1 l l']
    congr 1
    funext A
    rw [c2 A l l']
  postprocess_prop := by
    intro V U _ pp m ε h
    rcases h with h | h
    · left; intro l l'; unfold privPostProcess; rw [h l l']
    · exact Or.inr h
  const_prop := by
    intro U _ u ε _
    left; intro l l'; rfl

noncomputable def sysPar (T : Type) : DPPar T :=
  { sys T with
    prop_par := by
      intro U V m1 m2 ε₁ ε₂ ε he f h1 h2
      by_cases hb : 1 ≤ ε
      · exact Or.inr hb
      have hb1 : ¬ 1 ≤ ε₁ := fun h => hb (he ▸ h.trans (le_max_left _ _))
      have hb2 : ¬ 1 ≤ ε₂ := fun h => hb (he ▸ h.trans (le_max_right _ _))
      have c1 : Cst m1 := h1.resolve_right hb1
      have c2 : Cst m2 := h2.resolve_right hb2
      left
      intro l l'
      unfold privParCompose
      rw [c1 _ (List.filter f l'), c2 _ (List.filter ((! ·) ∘ f) l')] }

/-- the deterministic length mechanism -/
noncomputable def mlen : Mechanism Unit ℕ := fun l => SPMF_pure l.length

theorem spmf_apply {α : Type} (p : SPMF α) (a : α) : p a = p.1 a := rfl

theorem ncst_of {T Z : Type} {m : Mechanism T Z} (l l' : List T) (x : Z) (h : (m l).1 x ≠ (m l').1 x) :
    ¬ Cst m := fun hc => h (by rw [hc l l'])

theorem mlen_ncst : ¬ Cst mlen := fun h => by
  have := congrArg (fun p : SPMF ℕ => p.1 0) (h [] [()])
  simp [mlen, probPure] at this

noncomputable def noiseless {T : Type} (dps : DPSystem T) : DPNoise dps where
  noise q _ _ _ l := SPMF_pure (q l)
  noise_priv _ _ _ := False
  noise_prop h := h.elim

theorem nb1 : Neighbour [()] [] := Neighbour.Deletion (a := []) (b := []) (n := ()) rfl rfl

theorem lenSens : sensitivity (fun l : List Unit => (l.length : ℤ)) 1 := by
  intro l₁ l₂ h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp <;> omega

theorem negq_unlucky (n : ℕ) : ¬ has_lucky (shift_qs n (fun A (_ : List Unit) => -(A : ℤ))) 0 := fun H => by
  rcases H 0 [] with ⟨K, HK⟩
  have := HK (K.toNat + 1) K le_rfl
  simp [shift_qs] at this
  omega

theorem nbN : Neighbour [1] ([] : List ℕ) := Neighbour.Deletion (a := []) (b := []) (n := 1) rfl rfl

theorem alg1 (n : ℕ) : ((3/2:ℝ)^n) ^ (2:ℝ) * (2⁻¹:ℝ)^(n+1) = 2⁻¹ * (9/8 : ℝ)^n := by
  rw [Real.rpow_two, ← pow_mul, pow_succ, show (9/8 : ℝ) = (3/2)^2 * 2⁻¹ by norm_num, mul_pow, ← pow_mul,
    mul_comm 2 n]
  ring

theorem alg2 (n : ℕ) : (3/2:ℝ)^n * (2⁻¹:ℝ)^(n+1) = 2⁻¹ * (3/4 : ℝ)^n := by
  rw [pow_succ, show (3/4 : ℝ) = (3/2) * 2⁻¹ by norm_num, mul_pow]
  ring

/-- geometric PMF on the naturals: n maps to 2⁻¹^(n+1) -/
noncomputable def geomPMF : PMF ℕ := ⟨fun n => (2⁻¹ : ENNReal) ^ (n+1), by
    rw [ENNReal.summable.hasSum_iff]
    simp_rw [pow_succ, ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)⟩

theorem geomPMF_toReal (n : ℕ) : (geomPMF n).toReal = (2⁻¹ : ℝ)^(n+1) := by
  show ((2⁻¹ : ENNReal) ^ (n+1)).toReal = _
  simp

instance mscTop (T : Type) : @MeasurableSingletonClass T ⊤ :=
  @MeasurableSingletonClass.mk T ⊤ (fun _ => MeasurableSpace.measurableSet_top)

/-- x^α · x^(1-α) = x for PMF values, any α -/
theorem rpow_self_split (x : ENNReal) (hx : x ≠ ⊤) (α : ℝ) : x ^ α * x ^ (1 - α) = x := by
  by_cases h0 : x = 0
  · subst h0
    rcases lt_trichotomy α 0 with h | h | h
    · rw [ENNReal.zero_rpow_of_pos (by linarith : (0:ℝ) < 1 - α)]; simp
    · subst h; simp
    · rw [ENNReal.zero_rpow_of_pos h]; simp
  · rw [← ENNReal.rpow_add _ _ h0 hx]; simp

end W1c0

namespace W1c0
open SLang

/-- restriction of a PMF to a set containing its support -/
noncomputable def restr {T : Type} (p : PMF T) (s : Set T) (h : Function.support p ⊆ s) : PMF s :=
  ⟨(⇑p) ∘ (↑), (hasSum_subtype_iff_of_support_subset h).2 (PMF.hasSum_coe_one p)⟩

theorem supp_sub {T : Type} (p q : PMF T) (hac : AbsCts p q) : Function.support p ⊆ q.support := by
  intro x hx; rw [PMF.mem_support_iff]; exact fun h => hx (hac x h)

theorem ac_restr {T : Type} (p q : PMF T) (hac : AbsCts p q) :
    AbsCts (restr p q.support (supp_sub p q hac)) (restr q q.support subset_rfl) :=
  fun x hx => hac x hx

theorem restr_eq_iff {T : Type} (p q : PMF T) (hac : AbsCts p q) :
    restr p q.support (supp_sub p q hac) = restr q q.support subset_rfl ↔ p = q := by
  constructor
  · intro he
    ext x
    by_cases hx : x ∈ q.support
    · have := congrArg (fun r : PMF q.support => r ⟨x, hx⟩) he
      exact this
    · rw [PMF.mem_support_iff, not_not] at hx
      rw [hx, hac x hx]
  · rintro rfl; rfl

theorem renyi_restr2 {U : Type} (p q : PMF U) (s : Set U) (hp : Function.support p ⊆ s)
    (hq : Function.support q ⊆ s) {α : ℝ} (hα : 1 < α) :
    RenyiDivergence (restr p s hp) (restr q s hq) α = RenyiDivergence p q α := by
  unfold RenyiDivergence RenyiDivergence_def
  congr 3
  refine tsum_subtype_eq_of_support_subset (s := s) (f := fun x => p x ^ α * q x ^ (1 - α)) ?_
  intro x hx
  by_contra hxs
  apply hx
  have h1 : p x = 0 := by by_contra h; exact hxs (hp (Function.mem_support.2 h))
  have h2 : q x = 0 := by by_contra h; exact hxs (hq (Function.mem_support.2 h))
  simp only [h1]
  rw [ENNReal.zero_rpow_of_pos (by linarith), zero_mul]

/-- Jensen for the ENNReal Renyi sum without countability: restrict to the support of q -/
theorem jens_nc {T : Type} [MeasurableSpace T] [MeasurableSingletonClass T] (p q : PMF T) {α : ℝ}
    (h : 1 < α) (H : AbsCts p q) :
    (∑' x : T, p x / q x * q x) ^ α ≤ ∑' x : T, (p x / q x) ^ α * q x := by
  let S : Set T := q.support
  haveI : Countable S := q.support_countable.to_subtype
  have hp : Function.support p ⊆ S := fun x hx => by
    rw [PMF.mem_support_iff]; intro hq; exact hx (H x hq)
  have hq : Function.support q ⊆ S := fun x hx => (PMF.mem_support_iff q x).mpr hx
  let p' : PMF S := ⟨fun x => p x, (hasSum_subtype_iff_of_support_subset hp).mpr (PMF.hasSum_coe_one p)⟩
  let q' : PMF S := ⟨fun x => q x, (hasSum_subtype_iff_of_support_subset hq).mpr (PMF.hasSum_coe_one q)⟩
  have s1 : Function.support (fun x => p x / q x * q x) ⊆ S := fun x hx => by
    rw [PMF.mem_support_iff]; intro h0; apply hx; simp [h0]
  have s2 : Function.support (fun x => (p x / q x) ^ α * q x) ⊆ S := fun x hx => by
    rw [PMF.mem_support_iff]; intro h0; apply hx; simp [h0]
  rw [← tsum_subtype_eq_of_support_subset s1, ← tsum_subtype_eq_of_support_subset s2]
  exact Renyi_Jensen_ENNReal p' q' h (fun x hx => H x hx)

/-- converse Jensen without countability (same restriction) -/
theorem conv_nc {T : Type} [MeasurableSpace T] [MeasurableSingletonClass T] (p q : PMF T) {α : ℝ}
    (h : 1 < α) (H : AbsCts p q)
    (Hsum : (∑' x : T, p x / q x * q x) ^ α = ∑' x : T, (p x / q x) ^ α * q x) : p = q := by
  let S : Set T := q.support
  haveI : Countable S := q.support_countable.to_subtype
  have hp : Function.support p ⊆ S := fun x hx => by
    rw [PMF.mem_support_iff]; intro hq; exact hx (H x hq)
  have hq : Function.support q ⊆ S := fun x hx => (PMF.mem_support_iff q x).mpr hx
  let p' : PMF S := ⟨fun x => p x, (hasSum_subtype_iff_of_support_subset hp).mpr (PMF.hasSum_coe_one p)⟩
  let q' : PMF S := ⟨fun x => q x, (hasSum_subtype_iff_of_support_subset hq).mpr (PMF.hasSum_coe_one q)⟩
  have s1 : Function.support (fun x => p x / q x * q x) ⊆ S := fun x hx => by
    rw [PMF.mem_support_iff]; intro h0; apply hx; simp [h0]
  have s2 : Function.support (fun x => (p x / q x) ^ α * q x) ⊆ S := fun x hx => by
    rw [PMF.mem_support_iff]; intro h0; apply hx; simp [h0]
  rw [← tsum_subtype_eq_of_support_subset s1, ← tsum_subtype_eq_of_support_subset s2] at Hsum
  have key : p' = q' := Renyi_Jensen_ENNReal_converse p' q' h (fun x hx => H x hx) Hsum
  ext x
  by_cases hx : x ∈ S
  · exact congrArg (fun r : PMF S => r ⟨x, hx⟩) key
  · have hq0 : q x = 0 := by
      by_contra hne; exact hx ((PMF.mem_support_iff q x).mpr hne)
    rw [hq0, H x hq0]

noncomputable def eps2 : NNReal := ⟨Real.log 2, Real.log_nonneg (by norm_num)⟩

theorem eps2_exp : Real.exp (eps2 : ℝ) = 2 := Real.exp_log (by norm_num)

/-- mass of true is (1/2)^(min n 5 + 1) for list length n -/
noncomputable def w (n : ℕ) (x : Bool) : ℝ :=
  if x then (1/2 : ℝ) ^ (min n 5 + 1) else 1 - (1/2 : ℝ) ^ (min n 5 + 1)

theorem w_pos (n : ℕ) (x : Bool) : 0 < w n x := by
  unfold w
  cases x
  · simp only [Bool.false_eq_true, if_false, sub_pos]
    exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  · simp only [if_true]; positivity

theorem w_sum (n : ℕ) : w n false + w n true = 1 := by
  unfold w; simp

theorem w_le (n n' : ℕ) (h : n' = n + 1 ∨ n = n' + 1) (x : Bool) : w n x ≤ 2 * w n' x := by
  rcases h with rfl | rfl
  · rcases Nat.lt_or_ge n 5 with hm | hm
    · interval_cases n <;> cases x <;> norm_num [w]
    · have e1 : min n 5 = 5 := min_eq_right hm
      have e2 : min (n + 1) 5 = 5 := min_eq_right (by omega)
      have := w_pos n x
      unfold w at this ⊢; rw [e1, e2] at *; cases x <;> simp only [Bool.false_eq_true, if_false, if_true] at * <;> linarith
  · rcases Nat.lt_or_ge n' 5 with hm | hm
    · interval_cases n' <;> cases x <;> norm_num [w]
    · have e1 : min n' 5 = 5 := min_eq_right hm
      have e2 : min (n' + 1) 5 = 5 := min_eq_right (by omega)
      have := w_pos n' x
      unfold w at this ⊢; rw [e1, e2] at *; cases x <;> simp only [Bool.false_eq_true, if_false, if_true] at * <;> linarith

noncomputable def q27 (l : List Unit) : PMF Bool :=
  ⟨fun x => ENNReal.ofReal (w l.length x), by
    rw [Summable.hasSum_iff ENNReal.summable, tsum_bool, ← ENNReal.ofReal_add (w_pos _ _).le
      (w_pos _ _).le, w_sum, ENNReal.ofReal_one]⟩

theorem nb_len {l₁ l₂ : List Unit} (h : Neighbour l₁ l₂) :
    l₂.length = l₁.length + 1 ∨ l₁.length = l₂.length + 1 := by
  cases h with
  | Addition h1 h2 => left; subst h1 h2; simp; omega
  | Deletion h1 h2 => right; subst h1 h2; simp; omega

theorem q27_dp : SLang.PureDP q27 eps2 := by
  intro l₁ l₂ hN S
  apply ENNReal.div_le_of_le_mul
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum (fun x => ?_)
  split_ifs
  · show ENNReal.ofReal (w l₁.length x) ≤ ENNReal.ofReal (Real.exp eps2) * ENNReal.ofReal (w l₂.length x)
    rw [eps2_exp, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (w_le _ _ (nb_len hN) x)
  · simp

theorem nbA : Neighbour ([] : List Unit) [()] := Neighbour.Addition (a := []) (b := []) (n := ()) rfl rfl

end W1c0

namespace W1c0
open SLang

theorem tsum_ite_pure_zero (P : sv4_state → Prop) [DecidablePred P] (X : sv4_state) (hX : ¬ P X) :
    (∑' a, if P a then probPure X a else 0) = 0 := by
  refine ENNReal.tsum_eq_zero.mpr (fun a => ?_)
  split_ifs with h1
  · simp only [probPure]
    split_ifs with h2
    · subst h2; exact absurd h1 hX
    · rfl
  · rfl

theorem tsum_ite_pure_one (P : sv4_state → Prop) [DecidablePred P] (X : sv4_state) (hX : P X) :
    (∑' a, if P a then probPure X a else 0) = 1 := by
  rw [tsum_eq_single X]
  · simp [hX, probPure]
  · intro b hb
    simp [probPure, hb]

end W1c0

namespace W1c0
open SLang

/-- noise that is constant on sensitive queries and exact otherwise; noise_priv always true -/
noncomputable def snoise (T : Type) : DPNoise (sys T) where
  noise q Δ _ _ := by classical exact if sensitivity q Δ then privConst 0 else fun l => SPMF_pure (q l)
  noise_priv _ _ _ := True
  noise_prop := by
    intro q Δ εn εd ε _ hs
    left
    intro l l'
    simp only [hs, if_true]
    rfl

/-- constant noise for the parallel system; noise_priv always true -/
noncomputable def cnoise (T : Type) : DPNoise (sysPar T).toDPSystem where
  noise _ _ _ _ := fun _ => SPMF_pure 0
  noise_priv _ _ _ := True
  noise_prop := by
    intros
    exact Or.inl (fun _ _ => rfl)

end W1c0

namespace W1c0
open SLang

/-- one bin holding everything -/
def B1 : Bins Unit ((1:ℕ+) : ℕ) := ⟨fun _ => 0⟩

theorem setc0 : setCount 1 B1 (emptyHistogram 1 B1) 0 0 = emptyHistogram 1 B1 := by
  first | rfl | decide | simp [emptyHistogram, setCount]

theorem setc1 : setCount 1 B1 (emptyHistogram 1 B1) 0 1 ≠ emptyHistogram 1 B1 := by
  intro he
  have := congrArg (fun h : Histogram Unit 1 B1 => h.count.toList) he
  simp [emptyHistogram, setCount] at this
  revert this; decide

end W1c0

namespace W1c0
open SLang

theorem hist_ne (h0 : 0 < ((1:ℕ+):ℕ)) :
    (privNoisedHistogramAux (dps := sys Unit) (dpn := noiseless (sys Unit)) 1 B1 1 1 0 h0 []).1
      (emptyHistogram 1 B1) ≠
    (privNoisedHistogramAux (dps := sys Unit) (dpn := noiseless (sys Unit)) 1 B1 1 1 0 h0 [()]).1
      (emptyHistogram 1 B1) := by
  simp only [privNoisedHistogramAux]
  unfold privNoisedBinCount noiseless
  simp [privPostProcess, privCompose, privComposeAdaptive, privConst, Bind.bind, Pure.pure, SLang.pure_bind,
    probPure]
  split_ifs with hA hB hB
  · have := congrArg (fun h : Histogram Unit 1 B1 => h.count.toList) hB
    revert this; decide
  · simp
  · exact (hA rfl).elim
  · exact (hA rfl).elim

theorem parhist_ne :
    (privParNoisedHistogramAux (dps := sysPar Unit) (dpn := noiseless (sysPar Unit).toDPSystem) 1 B1 1 1 0
      (by decide) []).1 (emptyHistogram 1 B1) ≠
    (privParNoisedHistogramAux (dps := sysPar Unit) (dpn := noiseless (sysPar Unit).toDPSystem) 1 B1 1 1 0
      (by decide) [()]).1 (emptyHistogram 1 B1) := by
  simp only [privParNoisedHistogramAux]
  unfold privParNoisedBinCount noiseless
  simp [privPostProcess, privParCompose, privConst, Bind.bind, Pure.pure, SLang.pure_bind, probPure]
  split_ifs with hA hB hB
  · have := congrArg (fun h : Histogram Unit 1 B1 => h.count.toList) hB
    revert this; decide
  · simp
  · exact (hA rfl).elim
  · exact (hA rfl).elim

end W1c0

open W1c0

-- `SLang.DPSystem.prop_adp` idx 8: necessary
theorem w0_1 : ¬ drop0% SLang.DPSystem.prop_adp 8 := fun h => by
  have := @h Unit (sys Unit) ℕ inferInstance mlen (1/2) (by norm_num) 0 [()] [] nb1 {1}
  simp [mlen, probPure, spmf_apply] at this
  all_goals norm_num at this

-- `SLang.DPSystem.adaptive_compose_prop` idx 11: necessary
theorem w0_2 : ¬ drop0% SLang.DPSystem.adaptive_compose_prop 11 := fun h => by
  have := (@h Unit (sys Unit) ℕ ℕ inferInstance inferInstance mlen (fun _ => privConst 0) 0 0 0
    (fun _ => Or.inl (fun _ _ => rfl)) (by simp)).resolve_right (by norm_num)
  refine ncst_of [] [()] (0, 0) ?_ this
  simp [privComposeAdaptive, privConst, mlen, Bind.bind, Pure.pure, SLang.pure_bind, probPure]

-- `SLang.DPSystem.postprocess_prop` idx 8: necessary
theorem w0_3 : ¬ drop0% SLang.DPSystem.postprocess_prop 8 := fun h => by
  have := (@h Unit (sys Unit) ℕ ℕ inferInstance id mlen 0).resolve_right (by norm_num)
  refine ncst_of [] [()] 0 ?_ this
  simp [privPostProcess, mlen, Bind.bind, Pure.pure, SLang.pure_bind, probPure]

-- `SLang.DPSystem.const_prop` idx 6: removable
theorem w0_4 : drop% SLang.DPSystem.const_prop 6 := by
  intro T self U inst u ε
  exact DPSystem.prop_mono (bot_le : (0:NNReal) ≤ ε) (DPSystem.const_prop (u := u) rfl)

-- `SLang.DPSystem.compose_prop` idx 11: necessary
theorem w0_5 : ¬ drop0% SLang.DPSystem.compose_prop 11 := fun h => by
  have := (@h Unit ℕ ℕ (sys Unit) _ _ mlen (privConst 0) 1 0 0 (Or.inr le_rfl)
    (Or.inl fun _ _ => rfl)).resolve_right (by norm_num)
  refine ncst_of [] [()] (0, 0) ?_ this
  simp [privCompose, privComposeAdaptive, privConst, mlen, Bind.bind, Pure.pure, SLang.pure_bind, probPure]

-- `SLang.DPSystem.compose_prop` idx 12: necessary
theorem w0_6 : ¬ drop0% SLang.DPSystem.compose_prop 12 := fun h => by
  have := (@h Unit ℕ ℕ (sys Unit) _ _ mlen (privConst 0) 0 0 0 (by simp)
    (Or.inl fun _ _ => rfl)).resolve_right (by norm_num)
  refine ncst_of [] [()] (0, 0) ?_ this
  simp [privCompose, privComposeAdaptive, privConst, mlen, Bind.bind, Pure.pure, SLang.pure_bind, probPure]

-- `SLang.DPSystem.compose_prop` idx 13: necessary
theorem w0_7 : ¬ drop0% SLang.DPSystem.compose_prop 13 := fun h => by
  have := (@h Unit ℕ ℕ (sys Unit) _ _ (privConst 0) mlen 0 0 0 (by simp)
    (Or.inl fun _ _ => rfl)).resolve_right (by norm_num)
  refine ncst_of [] [()] (0, 0) ?_ this
  simp [privCompose, privComposeAdaptive, privConst, mlen, Bind.bind, Pure.pure, SLang.pure_bind, probPure]

-- `SLang.DPSystem_prop_ext` idx 6: necessary
theorem w0_8 : ¬ drop0% SLang.DPSystem_prop_ext 6 := fun h =>
  mlen_ncst ((@h Unit ℕ (sys Unit) 1 0 mlen (Or.inr le_rfl)).resolve_right (by norm_num))

-- `SLang.DPPar.prop_par` idx 11: necessary
theorem w0_9 : ¬ drop0% SLang.DPPar.prop_par 11 := fun h => by
  have := (@h Unit (sysPar Unit) ℕ ℕ mlen (privConst 0) 0 0 0 (by simp) (fun _ => true)
    (Or.inl (fun _ _ => rfl))).resolve_right (by norm_num)
  refine ncst_of [] [()] (0, 0) ?_ this
  simp [privParCompose, privConst, mlen, Bind.bind, Pure.pure, SLang.pure_bind, probPure]

-- `SLang.ApproximateDP_gt1` idx 5: necessary
theorem w0_10 : ¬ drop0% SLang.ApproximateDP_gt1 5 := fun h => by
  have := @h Unit ℕ mlen 0 0 [()] [] nb1 {1}
  simp [mlen, probPure, spmf_apply] at this

-- `SLang.ENNReal.HasSum_fiberwise` idx 4: necessary
theorem w0_11 : ¬ drop0% SLang.ENNReal.HasSum_fiberwise 4 := fun h => by
  have := @h Unit Unit (fun _ => 0) 1 id
  simp only [tsum_zero] at this
  exact absurd (this.unique hasSum_zero) one_ne_zero

-- `SLang.PureDP_privConst` idx 4: removable
theorem w0_12 : drop% SLang.PureDP_privConst 4 := by
  intro T U u ε
  exact PureDP_mono (bot_le : (0:NNReal) ≤ ε) (PureDP_privConst (T := T) u 0 rfl)

-- `SLang.event_to_singleton` idx 4: necessary
theorem w0_13 : ¬ drop0% SLang.event_to_singleton 4 := fun h => by
  have := @h Unit ℕ mlen 0 [()] [] nb1 1
  simp [mlen, probPure, spmf_apply] at this

-- `SLang.PureDP_mono` idx 6: necessary
theorem w0_14 : ¬ drop0% SLang.PureDP_mono 6 := fun h => by
  have := @h Unit ℕ mlen 0 0 le_rfl [()] [] nb1 {1}
  simp [mlen, probPure, spmf_apply] at this

-- `SLang.pure_ApproximateDP` idx 7: necessary
theorem w0_15 : ¬ drop0% SLang.pure_ApproximateDP 7 := fun h => by
  have := @h Unit ℕ _ mlen (1/2) (by norm_num) 0 [()] [] nb1 {1}
  simp [mlen, probPure, spmf_apply] at this
  all_goals norm_num at this

-- `SLang.privParCompose_DP_Bound` idx 8: necessary
theorem w0_16 : ¬ drop0% SLang.privParCompose_DP_Bound 8 := fun h => by
  have := @h Unit ℕ ℕ mlen (privConst 0) 0 0 (fun _ => true) privConst_DP_Bound [()] [] nb1 {(1, 0)}
  simp [privParCompose, privConst, mlen, Bind.bind, Pure.pure, SLang.pure_bind, probPure, spmf_apply] at this

-- `SLang.privParCompose_DP_Bound` idx 9: necessary
theorem w0_17 : ¬ drop0% SLang.privParCompose_DP_Bound 9 := fun h => by
  have := @h Unit ℕ ℕ (privConst 0) mlen 0 0 (fun _ => false) privConst_DP_Bound [()] [] nb1 {(0, 1)}
  simp [privParCompose, privConst, mlen, Bind.bind, Pure.pure, SLang.pure_bind, probPure, spmf_apply] at this

-- `SLang.pureDP_priv_Par` idx 10: necessary
theorem w0_18 : ¬ drop0% SLang.pureDP_priv_Par 10 := fun h => by
  have := @h Unit ℕ ℕ mlen (privConst 0) 0 0 0 (by simp) (fun _ => true) privConst_DP_Bound [()] [] nb1 {(1, 0)}
  simp [privParCompose, privConst, mlen, Bind.bind, Pure.pure, SLang.pure_bind, probPure, spmf_apply] at this

-- `SLang.PureDP_PostProcess` idx 6: necessary
theorem w0_19 : ¬ drop0% SLang.PureDP_PostProcess 6 := fun h => by
  have := @h ℕ ℕ Unit id mlen 0 [()] [] nb1 {1}
  simp [privPostProcess, mlen, Bind.bind, Pure.pure, SLang.pure_bind, probPure, spmf_apply] at this

-- `SLang.Hsens_cov_τ_lemma` idx 7: necessary
theorem w0_20 : ¬ drop0% SLang.Hsens_cov_τ_lemma 7 := fun h => by
  have := h (sv_T := Unit) (fun _ l => (l.length : ℤ)) (l₁ := [(), ()]) (l₂ := []) (H := []) (v0 := 0)
    (fun _ => lenSens)
  simp [sv8_sum] at this

-- `SLang.Hsens_cov_τ` idx 7: necessary
theorem w0_21 : ¬ drop0% SLang.Hsens_cov_τ 7 := fun h => by
  have := h (sv_T := Unit) (fun _ l => (l.length : ℤ)) (fun _ => lenSens) 0 [] [(), ()] []
  simp [cov_τ_def, sv8_G, sv8_sum, sens_cov_τ] at this

-- `SLang.Hsens_cov_vk` idx 8: necessary
theorem w0_22 : ¬ drop0% SLang.Hsens_cov_vk 8 := fun h => by
  have hs : ∀ i : ℕ, sensitivity (fun l : List Unit => if i = 0 then (0:ℤ) else (l.length : ℤ)) 1 := by
    intro i
    by_cases hi : i = 0
    · simp only [hi, if_true]; intro l₁ l₂ _; simp
    · simp only [hi, if_false]; exact lenSens
  have := h (sv_T := Unit) (fun i l => if i = 0 then (0:ℤ) else (l.length : ℤ)) hs 0 [] [] [(), (), (), ()] 0
  simp [cov_vk_def, cov_τ_def, sv8_G, sv8_sum, sens_cov_vk, sens_cov_τ] at this

-- `SLang.sv9_aboveThresh_pmf_DP` idx 6: necessary
theorem w0_23 : ¬ indep0% SLang.sv9_aboveThresh_pmf_DP 6 := fun h => by
  have := h (sv_T := Unit) (fun A _ => -(A : ℤ)) 0 1 1 (fun _ l₁ l₂ _ => by simp [sensitivity]) 1 (by simp)
  have e : shift_qs 0 (fun (A : ℕ) (_ : List Unit) => -(A : ℤ)) = (fun (A : ℕ) (_ : List Unit) => -(A : ℤ)) := by
    funext A l; simp [shift_qs]
  apply negq_unlucky 0
  rw [e]
  exact this

-- `SLang.tsum_eq_tsum_of_ne_zero_bij` idx 8: necessary
theorem w0_24 : ¬ drop0% SLang.tsum_eq_tsum_of_ne_zero_bij 8 := fun h => by
  have := h (α := ℕ) (β := Unit) (γ := Bool) (f := fun _ => 1) (g := fun _ => 1)
    (fun _ => ()) (fun x _ => ⟨⟨true, by simp⟩, rfl⟩) (fun _ => rfl)
  simp at this

-- `SLang.tsum_eq_tsum_of_ne_zero_bij` idx 10: necessary
theorem w0_25 : ¬ drop0% SLang.tsum_eq_tsum_of_ne_zero_bij 10 := fun h => by
  have := h (α := ℕ) (β := Unit) (γ := Unit) (f := fun _ => 0) (g := fun _ => 1)
    (fun _ => ()) (fun x y _ => Subsingleton.elim _ _) (by simp)
  simp at this

-- `SLang.probBind_congr_strong` idx 5: necessary
theorem w0_26 : ¬ drop0% SLang.probBind_congr_strong 5 := fun h => by
  have := congrFun (@h Unit Bool (probPure ()) (fun _ => probPure true) (fun _ => probPure false)) true
  simp [Bind.bind, probBind, probPure] at this

-- `SLang.iSup_geo_cdf_ge_one` idx 1: necessary
theorem w0_27 : ¬ drop0% SLang.iSup_geo_cdf_ge_one 1 := fun h => by
  have := h 0
  simp [geo_cdf] at this

-- `PMF_AbsCts` idx 5: necessary
theorem w0_28 : ¬ drop0% PMF_AbsCts 5 := fun h => by
  have := @h Bool _ _ (PMF.pure true) (PMF.pure false) true (by simp)
  simp at this

-- `PMF_AbsCts` idx 2: necessary
theorem w0_29 : ¬ drop0% PMF_AbsCts 2 := fun h => by
  have heq : @PMF.toMeasure Bool ⊥ (PMF.pure true) = @PMF.toMeasure Bool ⊥ (PMF.pure false) := by
    apply @MeasureTheory.Measure.ext Bool ⊥
    intro s hs
    rcases MeasurableSpace.measurableSet_bot_iff.mp hs with rfl | rfl
    · simp
    · rw [@MeasureTheory.measure_univ _ ⊥ _ (@PMF.toMeasure.isProbabilityMeasure Bool ⊥ _),
        @MeasureTheory.measure_univ _ ⊥ _ (@PMF.toMeasure.isProbabilityMeasure Bool ⊥ _)]
  have := @h Bool ⊥ (PMF.pure true) (PMF.pure false) (heq ▸ MeasureTheory.Measure.AbsolutelyContinuous.rfl)
    true (by simp)
  simp at this

-- `EReal_sub_one_pos_of_one_lt` idx 1: necessary
theorem w0_30 : ¬ drop0% EReal_sub_one_pos_of_one_lt 1 := fun h => by
  have := h (α := 0)
  rw [EReal_coe_sub_one] at this
  have := EReal.coe_pos.mp this
  norm_num at this

-- `RenyiDivergenceExpectation` idx 5: necessary
theorem w0_31 : ¬ drop0% RenyiDivergenceExpectation 5 := fun h => by
  have := @h Unit (fun _ => 1) (fun _ => 0) 2 (by norm_num)
  norm_num [tsum_fintype, ENNReal.zero_rpow_of_neg, ENNReal.top_rpow_of_pos] at this

-- `ENNReal_rpow_sub_one_mul` idx 2: necessary
theorem w0_32 : ¬ drop0% ENNReal_rpow_sub_one_mul 2 := fun h => by
  have := h 0 (α := 0) (by simp)
  norm_num [ENNReal.zero_rpow_of_neg] at this

-- `Integrable_rpow` idx 3: removable
theorem w0_33 : drop% Integrable_rpow 3 := by
  intro T _ f μ α mem h1 h2
  have Z := mem.integrable_norm_rpow h1 h2
  refine Z.mono' ((Real.continuous_rpow_const ENNReal.toReal_nonneg).comp_aestronglyMeasurable
    mem.aestronglyMeasurable) ?_
  refine MeasureTheory.ae_of_all _ (fun x => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact Real.abs_rpow_le_abs_rpow _ _

-- `Integrable_rpow` idx 6: necessary
theorem w0_34 : ¬ drop0% Integrable_rpow 6 := fun h => by
  have := h (T := ℕ) (fun _ => (1:ℝ)) (fun _ => zero_le_one) MeasureTheory.Measure.count 1
    one_ne_zero ENNReal.one_ne_top
  simp [MeasureTheory.integrable_const_iff] at this
  have h2 := this.measure_univ_lt_top
  simp [MeasureTheory.Measure.count_univ] at h2

-- `Integrable_rpow` idx 7: necessary
theorem w0_35 : ¬ drop0% Integrable_rpow 7 := fun h => by
  have := h (T := ℕ) (fun _ => (0:ℝ)) (fun _ => le_rfl) MeasureTheory.Measure.count 0
    (MeasureTheory.MemLp.zero) ENNReal.zero_ne_top
  simp [MeasureTheory.integrable_const_iff] at this
  have h2 := this.measure_univ_lt_top
  simp [MeasureTheory.Measure.count_univ] at h2

-- `RenyiDivergenceExpectation'_pointwise` idx 3: removable
theorem w0_36 : drop% RenyiDivergenceExpectation'_pointwise 3 := by
  intro a b α ha hat
  rcases lt_trichotomy α 1 with h | h | h
  · have hapos : a ^ α ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 ha) hat).ne'
    rcases eq_or_ne b 0 with hb0 | hb0
    · subst hb0
      rw [ENNReal.zero_rpow_of_pos (by linarith), ENNReal.div_zero ha, ENNReal.top_rpow_of_neg (by linarith)]
      simp
    rcases eq_or_ne b ⊤ with hbt | hbt
    · subst hbt
      rw [ENNReal.top_rpow_of_pos (by linarith), ENNReal.div_top, ENNReal.zero_rpow_of_neg (by linarith),
        ENNReal.mul_top hapos, ENNReal.top_mul ha]
    · rw [div_eq_mul_inv, ENNReal.mul_rpow_of_ne_top hat (ENNReal.inv_ne_top.mpr hb0),
        ENNReal.inv_rpow, ← ENNReal.rpow_neg, mul_right_comm, ENNReal_rpow_sub_one_mul a ha hat, neg_sub]
  · subst h; simp
  · exact RenyiDivergenceExpectation'_pointwise a b h ha hat

-- `eexp_rpow_eq_eexp_mul` idx 1: removable
theorem w0_37 : drop% eexp_rpow_eq_eexp_mul 1 := by
  intro β ε
  rcases lt_trichotomy β 0 with hb | hb | hb
  · induction ε
    · show ENNReal.eexp (⊤ : EReal) ^ β = ENNReal.eexp ((⊤ : EReal) * β.toEReal)
      rw [ENNReal.eexp_top, ENNReal.top_rpow_of_neg hb, EReal.top_mul_of_neg (EReal.coe_neg'.mpr hb)]
      simp
    · rename_i r
      have Hcast : ((r : ENNReal).toEReal) = ((r : ℝ) : EReal) := rfl
      rw [Hcast, ENNReal.eexp_ofReal, ← EReal.coe_mul, ENNReal.eexp_ofReal,
        ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
  · subst hb; simp [ENNReal.eexp_zero]
  · exact eexp_rpow_eq_eexp_mul hb ε

-- `continuousOn_rpow_Ici_of_one_lt` idx 1: necessary
theorem w0_38 : ¬ drop0% continuousOn_rpow_Ici_of_one_lt 1 := fun h => by
  have hc := (h (α := -1)).mono (Set.Icc_subset_Ici_self : Set.Icc (0:ℝ) 1 ⊆ Set.Ici 0)
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hc
  have hx : (1 / (|M| + 1) : ℝ) ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by positivity, by rw [div_le_one (by positivity)]; linarith [abs_nonneg M]⟩
  have := hM ⟨_, hx, rfl⟩
  simp only [Real.rpow_neg_one, one_div, inv_inv] at this
  linarith [le_abs_self M]

-- `Integrable_rpow_of_one_lt` idx 4: necessary
theorem w0_39 : ¬ drop0% Integrable_rpow_of_one_lt 4 := fun h => by
  have := h (T := ℕ) (f := fun _ => (0:ℝ)) (α := 0) (fun _ => le_rfl) (μ := MeasureTheory.Measure.count)
    (by rw [ENNReal.ofReal_zero]; exact MeasureTheory.MemLp.zero)
  simp [MeasureTheory.integrable_const_iff] at this
  have h2 := this.measure_univ_lt_top
  simp [MeasureTheory.Measure.count_univ] at h2

-- `Integrable_rpow_of_one_lt` idx 7: necessary
theorem w0_40 : ¬ drop0% Integrable_rpow_of_one_lt 7 := fun h => by
  have := h (T := ℕ) (f := fun _ => (1:ℝ)) (α := 2) (by norm_num) (fun _ => zero_le_one)
    (μ := MeasureTheory.Measure.count)
  simp [MeasureTheory.integrable_const_iff] at this
  have h2 := this.measure_univ_lt_top
  simp [MeasureTheory.Measure.count_univ] at h2

-- `Integrable_of_MemLp_one_lt` idx 4: necessary
theorem w0_41 : ¬ drop0% Integrable_of_MemLp_one_lt 4 := fun h => by
  have := @h ℝ _ (fun x => x ^ (-1 : ℝ)) 0 (MeasureTheory.volume.restrict (Set.Ioo 0 1)) inferInstance
    (by rw [ENNReal.ofReal_zero, MeasureTheory.memLp_zero_iff_aestronglyMeasurable]
        exact (measurable_id.pow_const _).aestronglyMeasurable)
  have h2 := (intervalIntegral.integrableOn_Ioo_rpow_iff (s := -1) (t := 1) one_pos).mp this
  norm_num at h2

-- `Renyi_Jensen_real` idx 6: necessary
theorem w0_42 : ¬ drop0% Renyi_Jensen_real 6 := fun h => by
  have := h (T := Bool) (fun b => if b then 1 else 0) (PMF.uniformOfFintype Bool) (1/2)
    (fun x => by cases x <;> simp) (MeasureTheory.MemLp.of_discrete)
  simp [tsum_fintype, PMF.uniformOfFintype_apply] at this
  have key : (2⁻¹:ℝ) < (2⁻¹:ℝ) ^ (2⁻¹:ℝ) := by
    simpa using Real.rpow_lt_rpow_of_exponent_gt (x := 2⁻¹) (by norm_num) (by norm_num)
      (show (2⁻¹:ℝ) < 1 by norm_num)
  linarith

-- `Renyi_Jensen_real` idx 7: necessary
theorem w0_43 : ¬ drop0% Renyi_Jensen_real 7 := fun h => by
  have := h (T := Bool) (fun b => if b then -1 else 0) (PMF.uniformOfFintype Bool) 3 (by norm_num)
    (MeasureTheory.MemLp.of_discrete)
  simp [tsum_fintype, PMF.uniformOfFintype_apply] at this
  norm_num at this

-- `Renyi_Jensen_strict_real` idx 2: removable
theorem w0_44 : drop% Renyi_Jensen_strict_real 2 := by
  intro T inst tc f q α h h2 mem hnz
  have Htrim : @PMF.toMeasure T inst q = (@PMF.toMeasure T ⊤ q).trim le_top := by
    ext s hs
    rw [MeasureTheory.trim_measurableSet_eq _ hs, PMF.toMeasure_apply _ hs,
      @PMF.toMeasure_apply T ⊤ q s MeasurableSpace.measurableSet_top]
  rw [Htrim] at mem
  exact @Renyi_Jensen_strict_real T ⊤ (mscTop T) tc f q α h h2 (MeasureTheory.memLp_of_memLp_trim le_top mem) hnz

-- `Renyi_Jensen_strict_real` idx 3: removable
theorem w0_45 : drop% Renyi_Jensen_strict_real 3 := by
  intro T inst msc f q α h h2 mem hnz
  haveI : Countable T := by
    have hc := q.support_countable
    rwa [show q.support = Set.univ from Set.eq_univ_of_forall (fun t => (PMF.mem_support_iff q t).mpr (hnz t)),
      Set.countable_univ_iff] at hc
  exact Renyi_Jensen_strict_real f q α h h2 mem hnz

-- `Renyi_Jensen_strict_real` idx 9: necessary
theorem w0_46 : ¬ drop0% Renyi_Jensen_strict_real 9 := fun h => by
  have := h (T := ℕ) (fun n => (3/2 : ℝ)^n) geomPMF 2 (by norm_num) (fun n => by positivity)
    (fun n => by show (2⁻¹ : ENNReal)^(n+1) ≠ 0; simp)
  rcases this with h1 | h1
  · simp only [geomPMF_toReal, alg1, alg2] at h1
    have hns : ¬ Summable (fun n : ℕ => 2⁻¹ * (9/8 : ℝ)^n) := by
      rw [summable_mul_left_iff (by norm_num), summable_geometric_iff_norm_lt_one]
      norm_num
    have hs : Summable (fun n : ℕ => 2⁻¹ * (3/4 : ℝ)^n) :=
      (summable_mul_left_iff (by norm_num)).mpr (summable_geometric_of_lt_one (by norm_num) (by norm_num))
    rw [tsum_eq_zero_of_not_summable hns] at h1
    have hpos : 0 < ∑' n : ℕ, 2⁻¹ * (3/4 : ℝ)^n :=
      hs.tsum_pos (fun n => by positivity) 0 (by norm_num)
    exact lt_asymm (Real.rpow_pos_of_pos hpos 2) h1
  · have a := h1 0
    have b := h1 1
    rw [← a] at b
    norm_num at b

-- `Renyi_Jensen_strict_real` idx 10: necessary
theorem w0_47 : ¬ drop0% Renyi_Jensen_strict_real 10 := fun h => by
  have := h (T := Bool) (fun b => if b then 1 else 0) (PMF.pure true) 2 (by norm_num)
    (fun x => by cases x <;> simp) (MeasureTheory.MemLp.of_discrete)
  simp [tsum_fintype, Bool.forall_bool] at this

-- `Renyi_Jensen_div_ne_top` idx 3: necessary
theorem w0_48 : ¬ drop0% Renyi_Jensen_div_ne_top 3 := fun h => by
  have := @h Bool (PMF.pure true) (PMF.pure false) (fun x hx => PMF.apply_ne_top _ _ hx.1) true
  simp at this

-- `Renyi_Jensen_div_ne_top` idx 4: removable
theorem w0_49 : drop% Renyi_Jensen_div_ne_top 4 := by
  intro T p q H a
  exact Renyi_Jensen_div_ne_top p q H (fun x hx => PMF.apply_ne_top _ _ hx.1) a

-- `PMF_div_mul_eq` idx 3: necessary
theorem w0_50 : ¬ drop0% PMF_div_mul_eq 3 := fun h => by
  have := @h Bool (PMF.pure true) (PMF.pure false) true
  simp at this

-- `Renyi_Jensen_rw` idx 6: removable
theorem w0_51 : drop% Renyi_Jensen_rw 6 := by
  intro T p q α h H x
  exact Renyi_Jensen_rw p q h H (fun x hx => PMF.apply_ne_top _ _ hx.1) x

-- `Renyi_Jensen_rw` idx 5: removable
theorem w0_52 : drop% Renyi_Jensen_rw 5 := by
  intro T p q α h Hs x
  by_cases hq : q x = 0
  · simp [hq]
  · unfold Renyi_Jensen_f
    rw [ENNReal.toReal_rpow, ← ENNReal.toReal_mul, ENNReal.ofReal_toReal]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith)
      (ENNReal.div_lt_top (PMF.apply_ne_top p x) hq).ne) (PMF.apply_ne_top q x)

-- `Renyi_Jensen_rw` idx 4: necessary
theorem w0_53 : ¬ drop0% Renyi_Jensen_rw 4 := fun h => by
  have := h (T := Bool) (PMF.pure true) (PMF.uniformOfFintype Bool) (α := -1) (fun x hx => by simp at hx)
    (fun x hx => PMF.apply_ne_top _ _ hx.1) false
  simp [PMF.uniformOfFintype_apply, ENNReal.zero_rpow_of_neg] at this

-- `Renyi_Jensen_f_MemLp` idx 9: removable
theorem w0_54 : drop% Renyi_Jensen_f_MemLp 9 := by
  intro T inst msc cnt p q α h H Hnts
  exact Renyi_Jensen_f_MemLp p q h H (fun x hx => PMF.apply_ne_top _ _ hx.1) Hnts

-- `Renyi_Jensen_ENNReal_reduct` idx 2: removable
theorem w0_55 : drop% Renyi_Jensen_ENNReal_reduct 2 := by
  intro T inst cnt p q α h H
  exact @Renyi_Jensen_ENNReal_reduct T ⊤ (mscTop T) cnt p q α h H

-- `Renyi_Jensen_ENNReal` idx 2: removable
theorem w0_56 : drop% Renyi_Jensen_ENNReal 2 := by
  intro T inst cnt p q α h H
  exact @Renyi_Jensen_ENNReal T ⊤ (mscTop T) cnt p q α h H

-- `Renyi_Jensen_ENNReal_converse_reduct` idx 2: removable
theorem w0_57 : drop% Renyi_Jensen_ENNReal_converse_reduct 2 := by
  intro T inst cnt p q α h H Hq Hs
  exact @Renyi_Jensen_ENNReal_converse_reduct T ⊤ (mscTop T) cnt p q α h H Hq Hs

-- `Renyi_Jensen_ENNReal_converse_reduct` idx 9: removable
theorem w0_58 : drop% Renyi_Jensen_ENNReal_converse_reduct 9 := by
  intro T inst msc cnt p q α h H Hs
  exact Renyi_Jensen_ENNReal_converse p q h H Hs

-- `Renyi_Jensen_ENNReal_converse_reduct` idx 10: necessary
theorem w0_59 : ¬ drop0% Renyi_Jensen_ENNReal_converse_reduct 10 := fun h =>
  absurd (@h Bool _ _ _ (PMF.pure true) (PMF.uniformOfFintype Bool) 2 (by norm_num)
    (fun x hx => by simp at hx) (fun t => by simp [PMF.uniformOfFintype_apply])) (by
      intro he
      have := congrArg (fun p : PMF Bool => p false) he
      simp at this
      exact absurd this.symm (by simp))

-- `reducedPMF_norm_acts` idx 3: necessary
theorem w0_60 : ¬ drop0% reducedPMF_norm_acts 3 := fun h => by
  have := @h Bool (PMF.pure true) (PMF.pure false)
  have hz : reducedPMF_def (PMF.pure true) (PMF.pure false) = fun _ => 0 := by
    funext x; obtain ⟨x, hx⟩ := x; cases x
    · simp [reducedPMF_def]
    · exact absurd (by simp [PMF.pure_apply] : (PMF.pure false : PMF Bool) true = 0) hx
  rw [hz] at this
  exact absurd (this.unique hasSum_zero) one_ne_zero

-- `reducedPMF_apply` idx 3: necessary
theorem w0_61 : ¬ indep0% reducedPMF_apply 3 := fun h => by
  have := h (T := Bool) (p := PMF.pure true) (q := PMF.pure false) (x := ⟨false, by simp⟩) true (by simp)
  simp at this

-- `reducedPMF_tsum_mul_eq` idx 3: necessary
theorem w0_62 : ¬ indep0% reducedPMF_tsum_mul_eq 3 := fun h => by
  have := h (T := Bool) (p := PMF.pure true) (q := PMF.pure false) (Hq := fun _ h => h)
    (f := fun _ _ => 0) true (by simp)
  simp at this

-- `RenyiDivergence_def_nonneg` idx 2: removable
theorem w0_63 : drop% RenyiDivergence_def_nonneg 2 := by
  intro T inst cnt p q hpq α hα
  exact @RenyiDivergence_def_nonneg T ⊤ (mscTop T) cnt p q hpq α hα

-- `RenyiDivergence_def_nonneg` idx 6: removable
theorem w0_64 : drop% RenyiDivergence_def_nonneg 6 := by
  intro T inst msc cnt p q α hα
  by_cases hac : AbsCts p q
  · exact RenyiDivergence_def_nonneg p q hac hα
  · obtain ⟨x, hqx, hpx⟩ : ∃ x, q x = 0 ∧ p x ≠ 0 := by simpa [AbsCts] using hac
    have hpos : p x ^ α ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hpx) (PMF.apply_ne_top p x)).ne'
    have hsum : ∑' x, p x ^ α * q x ^ (1 - α) = ⊤ := ENNReal.tsum_eq_top_of_eq_top
      ⟨x, by rw [hqx, ENNReal.zero_rpow_of_neg (by linarith)]; exact ENNReal.mul_top hpos⟩
    simp only [RenyiDivergence_def, hsum]
    rw [show ENNReal.elog ⊤ = ⊤ from rfl, EReal.mul_top_of_pos]
    · exact le_top
    · exact_mod_cast inv_pos.2 (sub_pos.2 hα)

-- `RenyiDivergence_def_log_sum_nonneg` idx 6: removable
theorem w0_65 : drop% RenyiDivergence_def_log_sum_nonneg 6 := by
  intro T inst msc cnt p q α hα
  by_cases hac : AbsCts p q
  · exact RenyiDivergence_def_log_sum_nonneg p q hac hα
  · obtain ⟨x, hqx, hpx⟩ : ∃ x, q x = 0 ∧ p x ≠ 0 := by simpa [AbsCts] using hac
    have hpos : p x ^ α ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hpx) (PMF.apply_ne_top p x)).ne'
    have hsum : ∑' x, p x ^ α * q x ^ (1 - α) = ⊤ := ENNReal.tsum_eq_top_of_eq_top
      ⟨x, by rw [hqx, ENNReal.zero_rpow_of_neg (by linarith)]; exact ENNReal.mul_top hpos⟩
    rw [hsum]
    exact le_top

-- `RenyiDivergence_def_nonneg` idx 8: necessary
theorem w0_66 : ¬ drop0% RenyiDivergence_def_nonneg 8 := fun h => by
  have := @h Bool _ _ _ (PMF.pure true) (PMF.uniformOfFintype Bool) (fun x hx => by simp at hx) (-1)
  have hsum : ∑' x, (PMF.pure true : PMF Bool) x ^ (-1:ℝ) * (PMF.uniformOfFintype Bool) x ^ (1 - (-1:ℝ)) = ⊤ :=
    ENNReal.tsum_eq_top_of_eq_top ⟨false, by simp [PMF.uniformOfFintype_apply, ENNReal.zero_rpow_of_neg]⟩
  simp only [RenyiDivergence_def, hsum] at this
  rw [show ENNReal.elog ⊤ = ⊤ from rfl, EReal.mul_top_of_neg] at this
  · simp at this
  · exact_mod_cast (by norm_num : ((-1:ℝ) - 1)⁻¹ < 0)

-- `RenyiDivergence_refl_zero` idx 3: removable
theorem w0_67 : drop% RenyiDivergence_refl_zero 3 := by
  intro T p α
  have e : ∀ x, p x ^ α * p x ^ (1 - α) = p x := fun x => rpow_self_split _ (PMF.apply_ne_top p x) α
  have hs : ∑' x, p x ^ α * p x ^ (1 - α) = 1 := by
    simp_rw [e]; exact PMF.tsum_coe p
  have e1 : ENNReal.elog 1 = 0 := by simpa using ENNReal.elog_of_pos_real (r := 1) one_pos
  simp [RenyiDivergence_def, hs, e1]

-- `RenyiDivergence_def_eq_0_iff` idx 7: necessary
theorem w0_68 : ¬ drop0% RenyiDivergence_def_eq_0_iff 7 := fun h => by
  have := @h Bool _ _ _ (PMF.pure true) (PMF.uniformOfFintype Bool) 1 (fun x hx => by simp at hx)
  have he := this.mp (by simp [RenyiDivergence_def])
  have := congrArg (fun r : PMF Bool => r false) he
  simp [PMF.uniformOfFintype_apply] at this
  exact absurd this.symm (by simp)

-- `RenyiDivergence_aux_zero` idx 7: necessary
theorem w0_69 : ¬ drop0% RenyiDivergence_aux_zero 7 := fun h => by
  have := @h Bool _ _ _ (PMF.pure true) (PMF.uniformOfFintype Bool) 1 (fun x hx => by simp at hx)
  have he := this.mpr (by simp [RenyiDivergence, RenyiDivergence_def])
  have := congrArg (fun r : PMF Bool => r false) he
  simp [PMF.uniformOfFintype_apply] at this
  exact absurd this.symm (by simp)

-- `RenyiDivergence_aux_zero` idx 8: removable
theorem w0_70 : drop% RenyiDivergence_aux_zero 8 := by
  intro T inst msc cnt p q α hα
  by_cases hac : AbsCts p q
  · exact RenyiDivergence_aux_zero p q hα hac
  · obtain ⟨x, hqx, hpx⟩ : ∃ x, q x = 0 ∧ p x ≠ 0 := by simpa [AbsCts] using hac
    have hpq : p ≠ q := fun e => hpx (e ▸ hqx)
    have hpos : p x ^ α ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hpx) (PMF.apply_ne_top p x)).ne'
    have hsum : ∑' x, p x ^ α * q x ^ (1 - α) = ⊤ := ENNReal.tsum_eq_top_of_eq_top
      ⟨x, by rw [hqx, ENNReal.zero_rpow_of_neg (by linarith)]; exact ENNReal.mul_top hpos⟩
    simp only [RenyiDivergence, RenyiDivergence_def, hsum, hpq, false_iff]
    rw [show ENNReal.elog ⊤ = ⊤ from rfl, EReal.mul_top_of_pos (by exact_mod_cast inv_pos.2 (sub_pos.2 hα))]
    simp

-- `RenyiDivergence_le_MaxDivergence` idx 6: necessary
theorem w0_71 : ¬ drop0% RenyiDivergence_le_MaxDivergence 6 := fun h => by
  have := @h Bool (PMF.pure true) (PMF.pure false) 0 2 (by norm_num)
  have hsum : ∑' x, (PMF.pure true : PMF Bool) x ^ (2:ℝ) * (PMF.pure false : PMF Bool) x ^ (1 - (2:ℝ)) = ⊤ :=
    ENNReal.tsum_eq_top_of_eq_top ⟨true, by norm_num [ENNReal.zero_rpow_of_neg]⟩
  simp only [RenyiDivergence, RenyiDivergence_def, hsum] at this
  rw [show ENNReal.elog ⊤ = ⊤ from rfl, EReal.mul_top_of_pos (by norm_num)] at this
  simp at this

-- `SLang.tsum_indicator_pure` idx 2: necessary
theorem w0_72 : ¬ drop0% SLang.tsum_indicator_pure 2 := fun h => by
  have := h ((([], 0), []) : sv4_state) ([], 1)
  rw [ENNReal.tsum_eq_zero.mpr (fun a => ?_)] at this
  · simp at this
  · rcases a with ⟨a1, a2⟩
    by_cases h1 : (([], 1) : sv1_state) = a1
    · subst h1; simp [probPure]
      rintro - h2
      have := congrArg (fun z : sv4_state => z.1.2) h2
      simp at this
    · simp
      intro h2; exact absurd h2 h1

-- `combineConcentrated` idx 5: necessary
theorem w0_73 : ¬ drop0% combineConcentrated 5 := fun h => by
  have H := @h (noiseless zCDPSystem) 1 1 1 0
  have H2 := (show zCDP _ _ from H).1 [1] [] nbN 1
  unfold privNoisedBoundedMean privNoisedBoundedSum privNoisedCount noiseless at H2
  simp [exactBoundedSum, exactCount, Bind.bind, Pure.pure, SLang.pure_bind, probPure, spmf_apply] at H2
  apply (show ¬ probPure (1:ℚ) 1 = 0 by simp [probPure])
  exact H2 (show probPure (0:ℚ) 1 = 0 by simp [probPure])

-- `SLang.privNoisedCount_DP` idx 6: necessary
theorem w0_74 : ¬ drop0% SLang.privNoisedCount_DP 6 := fun h => by
  have := (@h Unit (sys Unit) (noiseless (sys Unit)) 1 1 0).resolve_right (by norm_num)
  refine ncst_of [] [()] 0 ?_ this
  unfold privNoisedCount noiseless
  simp [exactCount, Bind.bind, Pure.pure, probPure]

-- `SLang.sv4_probWhileCut_succ_false` idx 8: necessary
theorem w0_75 : ¬ drop0% SLang.sv4_probWhileCut_succ_false 8 := fun h => by
  have := congrFun (h (sv_T := Unit) (fun _ _ => 0) 0 1 [] 0 ([], 0) []) (([], 0), [])
  simp [probWhileCut, probWhileFunctional, sv4_aboveThreshC, sv1_aboveThreshC, sv4_aboveThreshF,
    sv1_threshold, sv1_noise, probZero, probPure, probBind] at this

-- `SLang.sv4_probWhileCut_succ` idx 9: necessary
theorem w0_76 : ¬ drop0% SLang.sv4_probWhileCut_succ 9 := fun h => by
  have := congrFun (h (sv_T := Unit) (fun _ _ => 0) 0 0 [] 0 ([], 0) 0 []) (([], 0), [0])
  simp [probWhileCut, probWhileFunctional, sv4_aboveThreshC, sv1_aboveThreshC, sv4_aboveThreshF,
    sv1_threshold, sv1_noise, probZero, probPure] at this
  exact this rfl

-- `SLang.sv5_sv6_loop_base_case` idx 12: necessary
theorem w0_77 : ¬ drop0% SLang.sv5_sv6_loop_base_case 12 := fun h => by
  have := h (sv_T := Unit) (fun _ _ => 0) 0 0 [] 1 0 [] [] 0 rfl rfl
  simp [sv5_loop, sv6_loop, sv6_cond_rec, sv4_aboveThreshC, sv1_aboveThreshC, sv1_threshold, sv1_noise,
    probZero, probWhileCut, probWhileFunctional] at this
  exact absurd (this.trans (tsum_ite_pure_zero _ _ (by simp))) one_ne_zero

-- `SLang.sv5_loop_ind` idx 11: necessary
theorem w0_78 : ¬ drop0% SLang.sv5_loop_ind 11 := fun h => by
  have := h (sv_T := Unit) (fun _ _ => 0) 0 0 [] 0 0 [] [] 0 0
  simp [sv5_loop, sv4_aboveThreshC, sv4_aboveThreshF, sv1_aboveThreshC, sv1_threshold, sv1_noise,
    probZero, probWhileCut, probWhileFunctional] at this
  exact absurd ((tsum_ite_pure_one _ _ (by simp)).symm.trans (this.trans (tsum_ite_pure_zero _ _ (by simp))))
    one_ne_zero

-- `SLang.sv5_sv6_loop_eq_point` idx 11: necessary
theorem w0_79 : ¬ drop0% SLang.sv5_sv6_loop_eq_point 11 := fun h => by
  have := h (sv_T := Unit) (fun _ _ => 0) 0 1 [] 1 0 [] [5] 0 rfl
  simp [sv5_loop, sv6_loop, sv6_cond_rec, sv4_aboveThreshC, sv4_aboveThreshF, sv1_aboveThreshC, sv1_threshold,
    sv1_noise, probZero, probWhileCut, probWhileFunctional, probBind] at this

-- `SLang.cone_constancy` idx 14: necessary
theorem w0_80 : ¬ drop0% SLang.cone_constancy 14 := fun h => by
  have := h (dps := sys ℕ) (dpn := noiseless (sys ℕ)) (sv_T := Unit) (qs := fun _ _ => 0) (T := 0)
    (ε₁ := 1) (ε₂ := 1) (τ := 0) (data := []) (v0 := 0) (vk := 0) 0 [] []
  simp [constancy_at, probWhileCut, probWhileFunctional, sv1_aboveThreshC, sv1_threshold, sv1_noise,
    probZero, probPure] at this
  exact this rfl

-- `SLang.cone_left_edge_constancy` idx 15: necessary
theorem w0_81 : ¬ drop0% SLang.cone_left_edge_constancy 15 := fun h => by
  have := h (dps := sys ℕ) (dpn := noiseless (sys ℕ)) (sv_T := Unit) (qs := fun _ _ => 0) (T := 0)
    (ε₁ := 1) (ε₂ := 1) (τ := 0) (data := []) (v0 := 0) (vk := 0) 0 [] [] rfl
  simp [constancy_at, probWhileCut, probWhileFunctional, sv1_aboveThreshC, sv1_threshold, sv1_noise,
    probZero, probPure] at this
  exact this rfl

-- `SLang.external_to_cone_zero` idx 14: necessary
theorem w0_82 : ¬ drop0% SLang.external_to_cone_zero 14 := fun h => by
  have := @h (sys ℕ) (noiseless (sys ℕ)) 1 [] [] Unit (fun _ _ => 0) 0 0 [] 1 1 0 0
  simp [probWhileCut, probWhileFunctional, sv1_aboveThreshC, sv1_threshold, sv1_noise,
    probZero, probPure] at this
  exact this rfl

-- `SLang.privSparseAux_DP` idx 11: necessary
theorem w0_83 : ¬ indep0% SLang.privSparseAux_DP 11 := fun h =>
  negq_unlucky 0 (h 0 1 1 (sv_T := Unit) (dps := sys Unit) (fun A _ => -(A : ℤ))
    (fun N H => absurd H (negq_unlucky N)) _ 0 rfl 0)

-- `SLang.privNoisedBinCount_DP` idx 8: necessary
theorem w0_84 : ¬ drop0% SLang.privNoisedBinCount_DP 8 := fun h => by
  have := (@h Unit 1 ⟨fun _ => 0⟩ (sys Unit) (noiseless (sys Unit)) 1 1 0 0).resolve_right (by norm_num)
  refine ncst_of [] [()] 0 ?_ this
  unfold privNoisedBinCount noiseless
  have e0 : exactBinCount (T := Unit) 1 ⟨fun _ => 0⟩ 0 [] = 0 := rfl
  have e1 : exactBinCount (T := Unit) 1 ⟨fun _ => 0⟩ 0 [()] = 1 := rfl
  simp only [e0, e1]
  simp [probPure]

-- `SLang.privParNoisedBinCount_DP` idx 8: necessary
theorem w0_85 : ¬ drop0% SLang.privParNoisedBinCount_DP 8 := fun h => by
  have := (@h Unit (sysPar Unit) (noiseless (sysPar Unit).toDPSystem) 1 ⟨fun _ => 0⟩ 1 1 0 0).resolve_right
    (by norm_num)
  refine ncst_of [] [()] 0 ?_ this
  unfold privParNoisedBinCount noiseless
  have e0 : exactBinCount (T := Unit) 1 ⟨fun _ => 0⟩ 0 [] = 0 := rfl
  have e1 : exactBinCount (T := Unit) 1 ⟨fun _ => 0⟩ 0 [()] = 1 := rfl
  simp only [e0, e1]
  simp [probPure]

-- `Renyi_Jensen_ENNReal_reduct` idx 3: removable
theorem w0_86 : drop% Renyi_Jensen_ENNReal_reduct 3 := by
  intro T inst msc p q α h H
  exact jens_nc p q h H

-- `Renyi_Jensen_ENNReal` idx 3: removable
theorem w0_87 : drop% Renyi_Jensen_ENNReal 3 := by
  intro T inst msc p q α h H
  exact jens_nc p q h H

-- `Renyi_Jensen_ENNReal_converse_reduct` idx 3: removable
theorem w0_88 : drop% Renyi_Jensen_ENNReal_converse_reduct 3 := by
  intro T inst msc p q α h H Hq Hs
  exact conv_nc p q h H Hs

-- `RenyiDivergence_aux_zero` idx 3: removable
theorem w0_89 : drop% RenyiDivergence_aux_zero 3 := by
  intro T inst msc p q α hα hac
  have : Countable q.support := q.support_countable.to_subtype
  rw [← renyi_restr2 p q q.support (supp_sub p q hac) subset_rfl hα, ← restr_eq_iff p q hac]
  exact @RenyiDivergence_aux_zero q.support ⊤ (mscTop _) _ _ _ α hα (ac_restr p q hac)

-- `SLang.PureDP_mono` idx 5: necessary
theorem w0_90 : ¬ drop0% SLang.PureDP_mono 5 := fun h => by
  have := @h Unit Bool q27 eps2 0 q27_dp [] [()] nbA {true}
  simp [q27, w] at this
  change ENNReal.ofReal (if (true = true) then (2⁻¹:ℝ) else 1 - 2⁻¹) /
    ENNReal.ofReal (if (true = true) then ((2:ℝ) ^ 2)⁻¹ else 1 - ((2:ℝ)^2)⁻¹) ≤ 1 at this
  simp only [ite_true] at this
  rw [ENNReal.div_le_iff (by norm_num) (by simp), one_mul, ENNReal.ofReal_le_ofReal_iff (by norm_num)] at this
  norm_num at this

-- `SLang.PureDP_ComposeAdaptive'` idx 8: necessary
theorem w0_91 : ¬ drop0% SLang.PureDP_ComposeAdaptive' 8 := fun h => by
  have := @h Unit ℕ ℕ mlen (fun _ => privConst 0) 0 0 0 (fun _ => privConst_DP_Bound) (by simp) [()] [] nb1 {(1, 0)}
  simp [privComposeAdaptive, privConst, mlen, Bind.bind, Pure.pure, SLang.pure_bind, probPure, spmf_apply] at this

-- `SLang.PureDP_ComposeAdaptive'` idx 9: necessary
theorem w0_92 : ¬ drop0% SLang.PureDP_ComposeAdaptive' 9 := fun h => by
  have := @h Unit ℕ ℕ (privConst 0) (fun _ => mlen) 0 0 0 privConst_DP_Bound (by simp) [()] [] nb1 {(0, 1)}
  simp [privComposeAdaptive, privConst, mlen, Bind.bind, Pure.pure, SLang.pure_bind, probPure, spmf_apply] at this

-- `SLang.PureDP_ComposeAdaptive'` idx 10: necessary
theorem w0_93 : ¬ drop0% SLang.PureDP_ComposeAdaptive' 10 := fun h => by
  have := @h Unit Bool ℕ q27 (fun _ => privConst 0) eps2 0 0 q27_dp (fun _ => privConst_DP_Bound) [] [()] nbA
    {(true, 0)}
  simp [privComposeAdaptive, privConst, q27, w, Bind.bind, Pure.pure, SLang.pure_bind, probPure, spmf_apply] at this
  rw [ENNReal.div_le_iff (by simp) (by simp), one_mul, ENNReal.inv_le_inv] at this
  norm_num at this

-- `SLang.pureDP_priv_Par` idx 8: necessary
theorem w0_94 : ¬ drop0% SLang.pureDP_priv_Par 8 := fun h => by
  have := @h Unit Bool ℕ q27 (privConst 0) eps2 0 0 (fun _ => true) q27_dp privConst_DP_Bound [] [()] nbA
    {(true, 0)}
  simp [privParCompose, privConst, q27, w, Bind.bind, Pure.pure, SLang.pure_bind, probPure, spmf_apply] at this
  rw [ENNReal.div_le_iff (by simp) (by simp), one_mul, ENNReal.inv_le_inv] at this
  norm_num at this

-- `SLang.sv5_sv6_loop_base_case` idx 11: removable
theorem w0_95 : drop% SLang.sv5_sv6_loop_base_case 11 := by
  intro sv_T qs T τ l point eval past future pres h1 h3
  subst h1
  rw [SLang.sv5_sv6_loop_base_case qs T τ l point 0 past [] pres rfl rfl h3]
  have key : ∀ n, probWhileCut (sv4_aboveThreshC qs T τ l) sv4_aboveThreshF (n + 1) ((past, pres), []) =
      probWhileCut (sv4_aboveThreshC qs T τ l) sv4_aboveThreshF 1 ((past, pres), []) := by
    intro n
    have hz : ∀ g : sv4_state → SLang sv4_state, probBind probZero g = probZero := fun g => by
      funext y; unfold probBind probZero; simp
    funext x
    simp [probWhileCut, probWhileFunctional, sv4_aboveThreshF, hz]
  unfold sv5_loop
  rw [key eval]

-- `SLang.DPNoise.noise_prop` idx 9: necessary
theorem w0_96 : ¬ drop0% SLang.DPNoise.noise_prop 9 := fun h => by
  have hns : ¬ sensitivity (fun l : List Unit => 2 * (l.length : ℤ)) 1 := fun hs => by
    have := hs [()] [] nb1; simp at this
  have := (@h Unit (sys Unit) (snoise Unit) (fun l => 2 * (l.length : ℤ)) 1 1 1 0 trivial).resolve_right
    (by norm_num)
  refine ncst_of [] [()] 0 ?_ this
  unfold snoise
  simp [hns, probPure]

-- `SLang.privParNoisedHistogramAux_DP` idx 10: necessary
theorem w0_97 : ¬ indep0% SLang.privParNoisedHistogramAux_DP 10 := fun h => by
  have := @h Unit (sysPar Unit) (cnoise Unit) 1 ⟨fun _ => 0⟩ 1 1 0 trivial 5
  simp at this

-- `Renyi_Jensen_f_MemLp` idx 8: removable
theorem w0_98 : drop% Renyi_Jensen_f_MemLp 8 := by
  intro T inst msc cnt p q α h Hspecial Hnts
  have : DiscreteMeasurableSpace T := MeasurableSingletonClass.toDiscreteMeasurableSpace
  have HRJf_nonneg (a : T) : 0 ≤ Renyi_Jensen_f p q a := ENNReal.toReal_nonneg
  have hp_ne_zero : ENNReal.ofReal α ≠ 0 := by simp; linarith
  have hp_ne_top : ENNReal.ofReal α ≠ ⊤ := by simp
  rw [MeasureTheory.memLp_iff]
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top]
  rw [ENNReal.toReal_ofReal (le_of_lt (lt_trans zero_lt_one h))]
  apply ENNReal.rpow_lt_top_of_nonneg (by positivity)
  rw [MeasureTheory.lintegral_countable']
  have Hsummand_eq : ∀ a : T,
      ‖Renyi_Jensen_f p q a‖ₑ ^ α * (PMF.toMeasure q) {a} = (p a / q a) ^ α * q a := by
    intro a
    by_cases hq : q a = 0
    · rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), hq, mul_zero, mul_zero]
    congr 1
    · show (‖Renyi_Jensen_f p q a‖₊ : ENNReal) ^ α = (p a / q a) ^ α
      rw [← Real.toNNReal_eq_nnnorm_of_nonneg (HRJf_nonneg a)]
      show (ENNReal.ofReal (Renyi_Jensen_f p q a)) ^ α = (p a / q a) ^ α
      rw [show Renyi_Jensen_f p q a = (p a / q a).toReal from rfl,
          ENNReal.ofReal_toReal (ENNReal.div_lt_top (PMF.apply_ne_top p a) hq).ne]
    · exact PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)
  simp_rw [Hsummand_eq]
  exact Hnts
  · apply MeasureTheory.StronglyMeasurable.aestronglyMeasurable
    apply Measurable.stronglyMeasurable
    apply Measurable.ennreal_toReal
    show Measurable (fun x => p x / q x)
    simp_rw [division_def]
    exact (Measurable.of_discrete).mul ((Measurable.of_discrete).inv)


-- `SLang.privNoisedHistogramAux_DP` idx 8: necessary
theorem w0_99 : ¬ drop0% SLang.privNoisedHistogramAux_DP 8 := fun h => by
  have := (@h Unit 1 B1 (sys Unit) (noiseless (sys Unit)) 1 1 0 0 (by norm_num)).resolve_right
    (by norm_num)
  exact ncst_of [] [()] (emptyHistogram 1 B1) (hist_ne _) this

-- `SLang.privNoisedHistogram_DP` idx 8: necessary
theorem w0_100 : ¬ drop0% SLang.privNoisedHistogram_DP 8 := fun h => by
  have := (@h Unit 1 B1 (sys Unit) (noiseless (sys Unit)) 1 1 0).resolve_right (by norm_num)
  exact ncst_of [] [()] (emptyHistogram 1 B1) (hist_ne (by decide)) this

-- `SLang.privParNoisedHistogramAux_DP` idx 8: necessary
theorem w0_101 : ¬ drop0% SLang.privParNoisedHistogramAux_DP 8 := fun h => by
  have := (@h Unit (sysPar Unit) (noiseless (sysPar Unit).toDPSystem) 1 B1 1 1 0 0 (by decide)).resolve_right
    (by norm_num)
  exact ncst_of [] [()] (emptyHistogram 1 B1) parhist_ne this

-- `SLang.privParNoisedHistogram_DP` idx 8: necessary
theorem w0_102 : ¬ drop0% SLang.privParNoisedHistogram_DP 8 := fun h => by
  have := (@h Unit (sysPar Unit) (noiseless (sysPar Unit).toDPSystem) 1 B1 1 1 0).resolve_right (by norm_num)
  exact ncst_of [] [()] (emptyHistogram 1 B1) parhist_ne this

-- `Integrable_of_MemLp_one_lt` idx 6: necessary
theorem w0_103 : ¬ drop0% Integrable_of_MemLp_one_lt 6 := fun h => by
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun n : ℕ => 1 / ((n:ℝ) + 1)) MeasureTheory.Measure.count :=
    measurable_from_nat.aestronglyMeasurable
  have hm : MeasureTheory.MemLp (fun n : ℕ => 1 / ((n:ℝ) + 1)) (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
    rw [show ENNReal.ofReal 2 = 2 by simp, MeasureTheory.memLp_two_iff_integrable_sq hmeas,
      MeasureTheory.integrable_count_iff]
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    refine this.congr (fun n => ?_)
    push_cast
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    field_simp
  have := @h ℕ _ (fun n : ℕ => 1 / ((n:ℝ) + 1)) 2 (by norm_num) MeasureTheory.Measure.count hm
  rw [MeasureTheory.integrable_count_iff] at this
  have h2 : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) := this.congr (fun n => by
    push_cast; rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)])
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp h2)

-- `Renyi_Jensen_f_MemLp` idx 7: removable
theorem w0_104 : drop% Renyi_Jensen_f_MemLp 7 := by
  intro T inst msc cnt p q α H Hspecial Hnts
  have : DiscreteMeasurableSpace T := MeasurableSingletonClass.toDiscreteMeasurableSpace
  have hmeas : MeasureTheory.AEStronglyMeasurable (Renyi_Jensen_f p q) (PMF.toMeasure q) := by
    apply MeasureTheory.StronglyMeasurable.aestronglyMeasurable
    apply Measurable.stronglyMeasurable
    apply Measurable.ennreal_toReal
    show Measurable (fun x => p x / q x)
    simp_rw [division_def]
    exact (Measurable.of_discrete).mul ((Measurable.of_discrete).inv)
  by_cases hα : 0 < α
  swap
  · rw [ENNReal.ofReal_of_nonpos (not_lt.mp hα), MeasureTheory.memLp_zero_iff_aestronglyMeasurable]
    exact hmeas
  have HRJf_nonneg (a : T) : 0 ≤ Renyi_Jensen_f p q a := ENNReal.toReal_nonneg
  have HRJf_nt := Renyi_Jensen_div_ne_top p q H Hspecial
  have hp_ne_zero : ENNReal.ofReal α ≠ 0 := by simp; linarith
  have hp_ne_top : ENNReal.ofReal α ≠ ⊤ := by simp
  rw [MeasureTheory.memLp_iff]
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top]
  rw [ENNReal.toReal_ofReal hα.le]
  apply ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.mpr hα.le)
  rw [MeasureTheory.lintegral_countable']
  have Hsummand_eq : ∀ a : T,
      ‖Renyi_Jensen_f p q a‖ₑ ^ α * (PMF.toMeasure q) {a} = (p a / q a) ^ α * q a := by
    intro a
    congr 1
    · show (‖Renyi_Jensen_f p q a‖₊ : ENNReal) ^ α = (p a / q a) ^ α
      rw [← Real.toNNReal_eq_nnnorm_of_nonneg (HRJf_nonneg a)]
      show (ENNReal.ofReal (Renyi_Jensen_f p q a)) ^ α = (p a / q a) ^ α
      rw [show Renyi_Jensen_f p q a = (p a / q a).toReal from rfl,
          ENNReal.ofReal_toReal (HRJf_nt a)]
    · exact PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)
  simp_rw [Hsummand_eq]
  exact Hnts
  · exact hmeas

namespace W1c0
open SLang
/-- two bins, everything in bin 1 -/
def B2 : Bins Unit ((2:ℕ+) : ℕ) := ⟨fun _ => 1⟩
end W1c0

-- `SLang.privMaxBinAboveThreshold_DP` idx 8: necessary
theorem w0_105 : ¬ drop0% SLang.privMaxBinAboveThreshold_DP 8 := fun h => by
  have := (@h Unit 2 B2 (sys Unit) (noiseless (sys Unit)) 1 1 0 0).resolve_right (by norm_num)
  refine ncst_of [] [()] none ?_ this
  have e : privMaxBinAboveThreshold (dps := sys Unit) (dpn := noiseless (sys Unit)) 2 B2 1 1 0 =
      privPostProcess (privNoisedHistogramAux (dps := sys Unit) (dpn := noiseless (sys Unit)) 2 B2 1 1 1
        (by decide)) (exactMaxBinAboveThresholdAux 2 B2 0 1 (by decide)) := rfl
  rw [e]
  simp only [privNoisedHistogramAux]
  unfold privNoisedBinCount noiseless
  simp [privPostProcess, privCompose, privComposeAdaptive, privConst, Bind.bind, Pure.pure, SLang.pure_bind,
    probPure]
  split_ifs with hA hB hB
  · exact absurd hB (by intro h; cases h)
  · simp
  · exact (hA rfl).elim
  · exact (hA rfl).elim

namespace W1c0
open SLang
/-- two bins over the naturals, everything in bin 1 -/
def BN : Bins ℕ ((2:ℕ+) : ℕ) := ⟨fun _ => 1⟩

/-- noise: constant for εn = 7 (then noise_priv holds), exact otherwise -/
noncomputable def mnoise : DPNoise (sys ℕ) where
  noise q _ εn _ := if εn = 7 then privConst 0 else fun l => SPMF_pure (q l)
  noise_priv εn _ _ := εn = 7
  noise_prop := by
    intro q Δ εn εd ε h _
    left
    intro l l'
    simp only [h, if_true]
    rfl

theorem nb5 : Neighbour [5] ([] : List ℕ) := Neighbour.Deletion (a := []) (b := []) (n := 5) rfl rfl
end W1c0

-- `SLang.privMeanHistogram_DP` idx 12: necessary
theorem w0_106 : ¬ drop0% SLang.privMeanHistogram_DP 12 := fun h => by
  have := (h (sys ℕ) mnoise 2 BN (fun _ => 1) 1 1 0 7 1 0 0 rfl).resolve_right (by norm_num)
  refine ncst_of [] [5] none ?_ this
  have e : privMaxBinAboveThreshold (dps := sys ℕ) (dpn := mnoise) 2 BN 1 1 0 =
      privPostProcess (privNoisedHistogramAux (dps := sys ℕ) (dpn := mnoise) 2 BN 1 1 1
        (by decide)) (exactMaxBinAboveThresholdAux 2 BN 0 1 (by decide)) := rfl
  unfold privMeanHistogram
  rw [e]
  simp only [privNoisedHistogramAux]
  unfold privNoisedBinCount privNoisedBoundedMean privNoisedBoundedSum privNoisedCount mnoise
  simp [privPostProcess, privCompose, privComposeAdaptive, privConst, Bind.bind, Pure.pure,
    SLang.pure_bind, probPure]
  split_ifs with hA hB hB
  · exact absurd hB (by intro h; cases h)
  · simp
  · exact (hA rfl).elim
  · exact (hA rfl).elim

-- `SLang.privMeanHistogram_DP` idx 13: necessary
theorem w0_107 : ¬ drop0% SLang.privMeanHistogram_DP 13 := fun h => by
  have := (h (sys ℕ) mnoise 2 BN (fun _ => 1) 7 1 (-1) 1 1 0 0 rfl).resolve_right (by norm_num)
  refine ncst_of [] [5] (some 0) ?_ this
  have e : privMaxBinAboveThreshold (dps := sys ℕ) (dpn := mnoise) 2 BN 7 1 (-1) =
      privPostProcess (privNoisedHistogramAux (dps := sys ℕ) (dpn := mnoise) 2 BN 7 1 1
        (by decide)) (exactMaxBinAboveThresholdAux 2 BN (-1) 1 (by decide)) := rfl
  unfold privMeanHistogram
  rw [e]
  simp only [privNoisedHistogramAux]
  unfold privNoisedBinCount privNoisedBoundedMean privNoisedBoundedSum privNoisedCount mnoise
  simp [privPostProcess, privCompose, privComposeAdaptive, privConst, Bind.bind, Pure.pure,
    SLang.pure_bind, probPure, exactBoundedSum, exactCount]
  intro _
  rfl

namespace W1c0
open SLang

/-- p restricted to the support of q, rescaled by s⁻¹ -/
noncomputable def scaleP {T : Type} (p q : PMF T) (s : ENNReal)
    (h : HasSum (fun x => p x / q x * q x * s⁻¹) 1) : PMF T := ⟨fun x => p x / q x * q x * s⁻¹, h⟩

theorem scaleP_apply {T : Type} (p q : PMF T) (s : ENNReal) (h : HasSum (fun x => p x / q x * q x * s⁻¹) 1)
    (x : T) : scaleP p q s h x = p x / q x * q x * s⁻¹ := rfl

/-- Jensen for the ENNReal Renyi sum without absolute continuity (rescale p on the support of q) -/
theorem jens_noac {T : Type} [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T] (p q : PMF T)
    {α : ℝ} (h : 1 < α) :
    (∑' x, p x / q x * q x) ^ α ≤ ∑' x, (p x / q x) ^ α * q x := by
  set s := ∑' x, p x / q x * q x with hs
  have hr : ∀ x, p x / q x * q x ≤ p x := fun x => by
    by_cases hq : q x = 0
    · simp [hq]
    · rw [ENNReal.div_mul_cancel hq (PMF.apply_ne_top q x)]
  have hs1 : s ≤ 1 := by
    rw [hs, ← PMF.tsum_coe p]; exact ENNReal.tsum_le_tsum hr
  have hst : s ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hs1
  rcases eq_or_ne s 0 with h0 | h0
  · rw [h0, ENNReal.zero_rpow_of_pos (by linarith)]; exact bot_le
  have hsum : HasSum (fun x => p x / q x * q x * s⁻¹) 1 := by
    rw [ENNReal.summable.hasSum_iff, ENNReal.tsum_mul_right]
    exact ENNReal.mul_inv_cancel h0 hst
  have hac : AbsCts (scaleP p q s hsum) q := fun x hx => by
    rw [scaleP_apply, hx]; simp
  have key := Renyi_Jensen_ENNReal (scaleP p q s hsum) q h hac
  have l1 : ∀ x, scaleP p q s hsum x / q x * q x = scaleP p q s hsum x := fun x => by
    by_cases hq : q x = 0
    · rw [hq, scaleP_apply, hq]; simp
    · exact ENNReal.div_mul_cancel hq (PMF.apply_ne_top q x)
  have r1 : ∀ x, (scaleP p q s hsum x / q x) ^ α * q x = (p x / q x) ^ α * q x * s⁻¹ ^ α := fun x => by
    by_cases hq : q x = 0
    · rw [hq]; simp
    · rw [scaleP_apply, ENNReal.div_mul_cancel hq (PMF.apply_ne_top q x), div_eq_mul_inv, div_eq_mul_inv,
        mul_right_comm, ENNReal.mul_rpow_of_nonneg _ _ (by linarith)]
      ring
  simp_rw [l1, PMF.tsum_coe, ENNReal.one_rpow, r1, ENNReal.tsum_mul_right] at key
  have hss : s ^ α * s⁻¹ ^ α = 1 := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by linarith), ENNReal.mul_inv_cancel h0 hst, ENNReal.one_rpow]
  calc s ^ α = s ^ α * 1 := (mul_one _).symm
    _ ≤ s ^ α * ((∑' x, (p x / q x) ^ α * q x) * s⁻¹ ^ α) := by gcongr
    _ = (∑' x, (p x / q x) ^ α * q x) * (s ^ α * s⁻¹ ^ α) := by ring
    _ = ∑' x, (p x / q x) ^ α * q x := by rw [hss, mul_one]

end W1c0

-- `Renyi_Jensen_ENNReal_reduct` idx 8: removable
theorem w0_108 : drop% Renyi_Jensen_ENNReal_reduct 8 := by
  intro T inst msc cnt p q α h
  exact jens_noac p q h

-- `Renyi_Jensen_ENNReal` idx 8: removable
theorem w0_109 : drop% Renyi_Jensen_ENNReal 8 := by
  intro T inst msc cnt p q α h
  exact jens_noac p q h

-- `Renyi_Jensen_f_MemLp` idx 2: necessary
theorem w0_110 : ¬ drop0% Renyi_Jensen_f_MemLp 2 := fun h => by
  have hq : ∀ x, (PMF.uniformOfFintype Bool) x ≠ 0 := fun x => by simp [PMF.uniformOfFintype_apply]
  have mem := @h Bool ⊥ _ (PMF.pure true) (PMF.uniformOfFintype Bool) 2 (by norm_num)
    (fun x hx => absurd hx (hq x)) (fun x hx => PMF.apply_ne_top _ _ hx.1) (by
      rw [tsum_fintype]
      exact ENNReal.sum_ne_top.mpr (fun x _ => ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
        (ENNReal.div_lt_top (PMF.apply_ne_top _ _) (hq x)).ne) (PMF.apply_ne_top _ _)))
  obtain ⟨g, hg, hfg⟩ := mem.aestronglyMeasurable
  obtain ⟨c, rfl⟩ := stronglyMeasurable_bot_iff.mp hg
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff] at hfg
  have hne : ∃ x, Renyi_Jensen_f (PMF.pure true) (PMF.uniformOfFintype Bool) x ≠ c := by
    by_cases hc : c = 0
    · refine ⟨true, ?_⟩
      subst hc
      simp [Renyi_Jensen_f, PMF.uniformOfFintype_apply]
    · exact ⟨false, fun e => hc (by rw [← e]; simp [Renyi_Jensen_f])⟩
  obtain ⟨x, hx⟩ := hne
  have hT := @MeasureTheory.measurableSet_toMeasurable Bool ⊥
    (@PMF.toMeasure Bool ⊥ (PMF.uniformOfFintype Bool))
    {x | ¬ Renyi_Jensen_f (PMF.pure true) (PMF.uniformOfFintype Bool) x = c}
  rcases MeasurableSpace.measurableSet_bot_iff.mp hT with h1 | h1
  · have := @MeasureTheory.subset_toMeasurable Bool ⊥ (@PMF.toMeasure Bool ⊥ (PMF.uniformOfFintype Bool))
      {x | ¬ Renyi_Jensen_f (PMF.pure true) (PMF.uniformOfFintype Bool) x = c}
    rw [h1] at this
    exact this hx
  · have := @MeasureTheory.measure_toMeasurable Bool ⊥ (@PMF.toMeasure Bool ⊥ (PMF.uniformOfFintype Bool))
      {x | ¬ Renyi_Jensen_f (PMF.pure true) (PMF.uniformOfFintype Bool) x = c}
    rw [h1, hfg, @MeasureTheory.measure_univ _ ⊥ _ (@PMF.toMeasure.isProbabilityMeasure Bool ⊥ _)] at this
    exact one_ne_zero this

namespace W1c0
open SLang

theorem one_sub_quarter : (1 : ENNReal) - 4⁻¹ = 3 * 4⁻¹ := by
  apply ENNReal.sub_eq_of_eq_add (by simp)
  rw [← add_one_mul, show (3:ENNReal) + 1 = 4 by norm_num, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]

/-- PMF on the naturals: n maps to 3 * 4⁻¹^(n+1) -/
noncomputable def qPMF : PMF ℕ := ⟨fun n => 3 * (4⁻¹ : ENNReal) ^ (n+1), by
    rw [ENNReal.summable.hasSum_iff]
    simp_rw [pow_succ, ← mul_assoc, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
      one_sub_quarter]
    first
      | exact ENNReal.mul_inv_cancel (by simp) (by simp)
      | (rw [mul_right_comm]; exact ENNReal.mul_inv_cancel (by simp) (ENNReal.mul_ne_top (by simp) (by simp)))⟩

theorem qPMF_ne (n : ℕ) : qPMF n ≠ 0 := by
  show 3 * (4⁻¹ : ENNReal) ^ (n+1) ≠ 0
  simp

theorem term_third (n : ℕ) : (geomPMF n / qPMF n) ^ (2:ℝ) * qPMF n = 3⁻¹ := by
  show ((2⁻¹ : ENNReal) ^ (n+1) / (3 * (4⁻¹ : ENNReal) ^ (n+1))) ^ (2:ℝ) * (3 * (4⁻¹ : ENNReal) ^ (n+1)) = 3⁻¹
  rw [ENNReal.rpow_two]
  rw [← ENNReal.toReal_eq_toReal_iff' (by simp [ENNReal.div_eq_top, ENNReal.mul_eq_top]) (by simp)]
  simp [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv]
  field_simp
  rw [← pow_mul, mul_comm (n+1) 2, pow_mul]
  norm_num

end W1c0

-- `Renyi_Jensen_f_MemLp` idx 10: necessary
theorem w0_111 : ¬ drop0% Renyi_Jensen_f_MemLp 10 := fun h => by
  have hac : AbsCts geomPMF qPMF := fun x hx => absurd hx (qPMF_ne x)
  have mem := h (T := ℕ) geomPMF qPMF (α := 2) (by norm_num) hac (fun x hx => PMF.apply_ne_top _ _ hx.1)
  rw [MeasureTheory.memLp_iff, MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp) (by simp),
    ENNReal.toReal_ofReal (by norm_num), MeasureTheory.lintegral_countable'] at mem
  have Hsummand_eq : ∀ a : ℕ, ‖Renyi_Jensen_f geomPMF qPMF a‖ₑ ^ (2:ℝ) * (PMF.toMeasure qPMF) {a} =
      (geomPMF a / qPMF a) ^ (2:ℝ) * qPMF a := by
    intro a
    congr 1
    · show (‖Renyi_Jensen_f geomPMF qPMF a‖₊ : ENNReal) ^ (2:ℝ) = (geomPMF a / qPMF a) ^ (2:ℝ)
      have HR : 0 ≤ Renyi_Jensen_f geomPMF qPMF a := ENNReal.toReal_nonneg
      rw [← Real.toNNReal_eq_nnnorm_of_nonneg HR]
      show (ENNReal.ofReal (Renyi_Jensen_f geomPMF qPMF a)) ^ (2:ℝ) = (geomPMF a / qPMF a) ^ (2:ℝ)
      rw [show Renyi_Jensen_f geomPMF qPMF a = (geomPMF a / qPMF a).toReal from rfl,
          ENNReal.ofReal_toReal (ENNReal.div_lt_top (PMF.apply_ne_top _ a) (qPMF_ne a)).ne]
    · exact PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)
  simp_rw [Hsummand_eq, term_third] at mem
  rw [ENNReal.tsum_const_eq_top_of_ne_zero (by simp), ENNReal.top_rpow_of_pos (by norm_num)] at mem
  exact lt_irrefl _ mem
  exact measurable_from_nat.aestronglyMeasurable

namespace W1c0
open SLang

theorem lap_val (q : List Unit → ℤ) (l : List Unit) (x : ℤ) :
    (privNoisedQueryPure q 1 1 1 l).1 x =
      ENNReal.ofReal (((Real.exp 1 - 1) / (Real.exp 1 + 1)) * Real.exp (-|x - q l|)) := by
  show DiscreteLaplaceGenSample (1 * 1) 1 (q l) x = _
  rw [DiscreteLaplaceGenSample_apply]
  norm_num

theorem lapC_pos : 0 < (Real.exp 1 - 1) / (Real.exp 1 + 1) :=
  div_pos (sub_pos.mpr (by have := Real.add_one_lt_exp (x := 1) one_ne_zero; linarith)) (by positivity)

theorem lap_contra {C u v ε : ℝ} (hC : 0 < C) (huv : ε + v < u)
    (h : ENNReal.ofReal (C * Real.exp u) / ENNReal.ofReal (C * Real.exp v) ≤ ENNReal.ofReal (Real.exp ε)) :
    False := by
  have hpos : 0 < C * Real.exp v := mul_pos hC (Real.exp_pos v)
  rw [ENNReal.div_le_iff (by simpa using hpos) ENNReal.ofReal_ne_top,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  have h2 : C * Real.exp u ≤ C * (Real.exp ε * Real.exp v) := by linarith
  have h3 := le_of_mul_le_mul_left h2 hC
  rw [← Real.exp_add, Real.exp_le_exp] at h3
  linarith

theorem dp_single {T U : Type} {m : Mechanism T U} {ε : ℝ} (h : DP m ε) (l₁ l₂ : List T)
    (hn : Neighbour l₁ l₂) (x : U) : (m l₁).1 x / (m l₂).1 x ≤ ENNReal.ofReal (Real.exp ε) := by
  have := h l₁ l₂ hn {x}
  convert this using 2 <;>
    (rw [tsum_eq_single x (fun b hb => by simp [hb]), if_pos (Set.mem_singleton x)]; try rfl)

end W1c0

-- `SLang.privNoisedQueryPure_DP` idx 6: necessary
theorem w0_112 : ¬ drop0% SLang.privNoisedQueryPure_DP 6 := fun h => by
  have H := @h Unit (fun l => (l.length : ℤ)) 1 1 1 0 lenSens
  have := dp_single H [()] [] nb1 1
  rw [lap_val, lap_val] at this
  exact lap_contra lapC_pos (by norm_num) this

-- `SLang.privNoisedQueryPure_DP` idx 7: necessary
theorem w0_113 : ¬ drop0% SLang.privNoisedQueryPure_DP 7 := fun h => by
  have H := @h Unit (fun l => 3 * (l.length : ℤ)) 1 1 1 1 (by simp [laplace_pureDP_noise_priv])
  have := dp_single H [()] [] nb1 3
  rw [lap_val, lap_val] at this
  exact lap_contra lapC_pos (by norm_num) this

-- `SLang.privNoisedQueryPure_DP_bound` idx 5: necessary
theorem w0_114 : ¬ drop0% SLang.privNoisedQueryPure_DP_bound 5 := fun h => by
  have H := @h Unit (fun l => 3 * (l.length : ℤ)) 1 1 1
  have := dp_single H [()] [] nb1 3
  rw [lap_val, lap_val] at this
  exact lap_contra lapC_pos (by norm_num) this

-- `Renyi_Jensen_f_MemLp` idx 3: removable
theorem w0_115 : drop% Renyi_Jensen_f_MemLp 3 := by
  intro T inst msc p q α h H Hspecial Hnts
  have hS : (q.support).Countable := q.support_countable
  have HRJf_nonneg (a : T) : 0 ≤ Renyi_Jensen_f p q a := ENNReal.toReal_nonneg
  have HRJf_nt := Renyi_Jensen_div_ne_top p q H Hspecial
  have hp_ne_zero : ENNReal.ofReal α ≠ 0 := by simp; linarith
  have hp_ne_top : ENNReal.ofReal α ≠ ⊤ := by simp
  -- a.e. strong measurability: f agrees a.e. with its restriction to the countable support
  have hg : Measurable (q.support.indicator (Renyi_Jensen_f p q)) := by
    intro B _
    by_cases h0 : (0:ℝ) ∈ B
    · have : q.support.indicator (Renyi_Jensen_f p q) ⁻¹' B =
          (q.support ∩ Renyi_Jensen_f p q ⁻¹' B) ∪ q.supportᶜ := by
        ext x; by_cases hx : x ∈ q.support <;> simp [hx, h0]
      rw [this]
      exact ((hS.mono Set.inter_subset_left).measurableSet).union hS.measurableSet.compl
    · have : q.support.indicator (Renyi_Jensen_f p q) ⁻¹' B = q.support ∩ Renyi_Jensen_f p q ⁻¹' B := by
        ext x; by_cases hx : x ∈ q.support <;> simp [hx, h0]
      rw [this]
      exact (hS.mono Set.inter_subset_left).measurableSet
  have hae : Renyi_Jensen_f p q =ᵐ[PMF.toMeasure q] q.support.indicator (Renyi_Jensen_f p q) := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null (t := q.supportᶜ) (fun x hx => ?_) ?_
    · intro hxs; exact hx (by simp [hxs])
    · rw [PMF.toMeasure_apply_eq_zero_iff _ hS.measurableSet.compl]
      exact disjoint_compl_right
  have hmeas : MeasureTheory.AEStronglyMeasurable (Renyi_Jensen_f p q) (PMF.toMeasure q) :=
    ⟨_, hg.stronglyMeasurable, hae⟩
  rw [MeasureTheory.memLp_iff]
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top]
  rw [ENNReal.toReal_ofReal (le_of_lt (lt_trans zero_lt_one h))]
  apply ENNReal.rpow_lt_top_of_nonneg (by positivity)
  rw [← PMF.restrict_toMeasure_support q, MeasureTheory.lintegral_countable _ hS]
  have Hsummand_eq : ∀ a : T,
      ‖Renyi_Jensen_f p q a‖ₑ ^ α * (PMF.toMeasure q) {a} = (p a / q a) ^ α * q a := by
    intro a
    congr 1
    · show (‖Renyi_Jensen_f p q a‖₊ : ENNReal) ^ α = (p a / q a) ^ α
      rw [← Real.toNNReal_eq_nnnorm_of_nonneg (HRJf_nonneg a)]
      show (ENNReal.ofReal (Renyi_Jensen_f p q a)) ^ α = (p a / q a) ^ α
      rw [show Renyi_Jensen_f p q a = (p a / q a).toReal from rfl,
          ENNReal.ofReal_toReal (HRJf_nt a)]
    · exact PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)
  simp_rw [Hsummand_eq]
  exact ne_top_of_le_ne_top Hnts (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective (fun a => (p a / q a) ^ α * q a))
  exact hmeas

-- `RenyiDivergence_le_MaxDivergence` idx 5: removable
theorem w0_116 : drop% RenyiDivergence_le_MaxDivergence 5 := by
  intro T p q ε α Hmax
  rcases lt_trichotomy α 1 with hα | rfl | hα
  swap
  · simp [RenyiDivergence, RenyiDivergence_def]
  swap
  · exact RenyiDivergence_le_MaxDivergence hα Hmax
  rcases eq_or_ne ε ⊤ with rfl | hεt
  · exact le_top
  lift ε to NNReal using hεt with r
  have Hm : ∀ t, p t / q t ≤ ENNReal.ofReal (Real.exp r) := fun t => by
    have := Hmax t
    have Hcast : ((r : ENNReal).toEReal) = ((r : ℝ) : EReal) := rfl
    rwa [Hcast, ENNReal.eexp_ofReal] at this
  set c := Real.exp ((α - 1) * r) with hc
  have term : ∀ x, ENNReal.ofReal c * p x ≤ p x ^ α * q x ^ (1 - α) := fun x => by
    rcases eq_or_ne (p x) 0 with hp | hp
    · rw [hp]; simp
    have hq : q x ≠ 0 := fun hq => by
      have := Hm x
      rw [hq, ENNReal.div_zero hp] at this
      exact ENNReal.ofReal_ne_top (top_le_iff.mp this)
    have hP : 0 < (p x).toReal := ENNReal.toReal_pos hp (PMF.apply_ne_top p x)
    have hQ : 0 < (q x).toReal := ENNReal.toReal_pos hq (PMF.apply_ne_top q x)
    have hm := Hm x
    rw [← ENNReal.ofReal_toReal (PMF.apply_ne_top p x), ← ENNReal.ofReal_toReal (PMF.apply_ne_top q x)] at hm ⊢
    set P := (p x).toReal
    set Q := (q x).toReal
    rw [ENNReal.div_le_iff (by simpa using hQ) ENNReal.ofReal_ne_top, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at hm
    rw [ENNReal.ofReal_rpow_of_pos hP, ENNReal.ofReal_rpow_of_pos hQ, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h1 : Real.exp (-r) * P ≤ Q := by
      rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]; linarith
    have h2 : (Real.exp (-r) * P) ^ (1 - α) ≤ Q ^ (1 - α) :=
      Real.rpow_le_rpow (by positivity) h1 (by linarith)
    rw [Real.mul_rpow (by positivity) hP.le, ← Real.exp_mul] at h2
    have h3 : P ^ α * P ^ (1 - α) = P := by rw [← Real.rpow_add hP]; simp
    have e1 : (α - 1) * (r:ℝ) = -r * (1 - α) := by ring
    calc c * P = Real.exp (-r * (1 - α)) * (P ^ α * P ^ (1 - α)) := by rw [h3, hc, e1]
      _ = P ^ α * (Real.exp (-r * (1 - α)) * P ^ (1 - α)) := by ring
      _ ≤ P ^ α * Q ^ (1 - α) := by gcongr
  have hS : ENNReal.ofReal c ≤ ∑' x, p x ^ α * q x ^ (1 - α) := by
    calc ENNReal.ofReal c = ∑' x, ENNReal.ofReal c * p x := by
          rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
      _ ≤ _ := ENNReal.tsum_le_tsum term
  unfold RenyiDivergence RenyiDivergence_def
  have hneg : α - 1 < 0 := by linarith
  rcases eq_or_ne (∑' x, p x ^ α * q x ^ (1 - α)) ⊤ with hSt | hSt
  · rw [hSt, show ENNReal.elog ⊤ = ⊤ from rfl, EReal.mul_top_of_neg (by exact_mod_cast inv_lt_zero.mpr hneg),
      ENNReal.ofEReal_bot]
    exact bot_le
  have hSpos : 0 < (∑' x, p x ^ α * q x ^ (1 - α)).toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le (by simp [c, Real.exp_pos]) hS)) hSt
  rw [← ENNReal.ofReal_toReal hSt, ENNReal.elog_of_pos_real hSpos, ← EReal.coe_mul, ENNReal.ofEReal_real,
    ← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  have hlog : (α - 1) * r ≤ Real.log (∑' x, p x ^ α * q x ^ (1 - α)).toReal := by
    rw [← Real.log_exp ((α - 1) * r)]
    exact Real.log_le_log (Real.exp_pos _) ((ENNReal.ofReal_le_iff_le_toReal hSt).mp hS)
  rw [← div_eq_inv_mul, div_le_iff_of_neg hneg]
  linarith
