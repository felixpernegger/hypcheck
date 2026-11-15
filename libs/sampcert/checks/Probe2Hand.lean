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

namespace Probe2
open SLang
def nq12 : SLang.Mechanism Unit Bool := fun l => if l = [] then SPMF_pure true else SPMF_pure false

open SLang

/-- mass function: uniform on Bool for the empty list, (3/4, 1/4) otherwise -/
noncomputable def mf (l : List Unit) (x : Bool) : ENNReal :=
  if l = [] then 2⁻¹ else if x then 4⁻¹ else 3 * 4⁻¹

theorem mf_sum (l : List Unit) : HasSum (mf l) 1 := by
  have h : ∑ b, mf l b = 1 := by
    rw [Fintype.sum_bool]
    unfold mf
    split
    · exact ENNReal.inv_two_add_inv_two
    · simp only [if_true, Bool.false_eq_true, if_false]
      calc (4:ENNReal)⁻¹ + 3 * 4⁻¹ = 4 * 4⁻¹ := by ring
        _ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  rw [← h]; exact hasSum_fintype _

theorem mf_ne (l : List Unit) (x : Bool) : mf l x ≠ 0 := by
  unfold mf; split
  · simp
  · cases x <;> simp

noncomputable def mech : SLang.Mechanism Unit Bool := fun l => ⟨mf l, mf_sum l⟩

theorem pp_val (l : List Unit) (x : Bool) : (SLang.privPostProcess mech id l).1 x = mf l x := by
  simp [privPostProcess, Bind.bind, Pure.pure, mech, probBind, probPure]

open SLang

theorem sq_rpow_half (x : ENNReal) : (x ^ 2) ^ (1/2 : ℝ) = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

theorem sq_rpow_inv_two (x : ENNReal) : (x ^ 2) ^ (2⁻¹ : ℝ) = x := by
  rw [← one_div]; exact sq_rpow_half x

theorem five_inv : (5 : ENNReal) * 5⁻¹ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

/-- masses (9/25, 16/25) for the empty list and (16/25, 9/25) otherwise, written as squares -/
noncomputable def sf (l : List Unit) (x : Bool) : ENNReal :=
  if (l = []) = x then (3 * 5⁻¹) ^ 2 else (4 * 5⁻¹) ^ 2

theorem sf_sum (l : List Unit) : HasSum (sf l) 1 := by
  have h : ∑ b, sf l b = 1 := by
    rw [Fintype.sum_bool]
    unfold sf
    have e : ((3:ENNReal) * 5⁻¹) ^ 2 + (4 * 5⁻¹) ^ 2 = (5 * 5⁻¹) ^ 2 := by ring
    by_cases hl : l = [] <;> simp [hl, e, add_comm, five_inv]
  rw [← h]; exact hasSum_fintype _

theorem sf_ne (l : List Unit) (x : Bool) : sf l x ≠ 0 := by
  unfold sf; split <;> simp

open SLang

noncomputable def eps4 : NNReal := ⟨Real.log 4, Real.log_nonneg (by norm_num)⟩

theorem eps4_exp : Real.exp (eps4 : ℝ) = 4 := Real.exp_log (by norm_num)
theorem eps4_exp_neg : Real.exp (-(eps4 : ℝ)) = 4⁻¹ := by rw [Real.exp_neg, eps4_exp]

theorem hqp4 : ∀ x : Unit, ENNReal.ofReal (Real.exp (-(eps4 : ℝ))) ≤
    (PMF.pure ()) x / (PMF.pure ()) x := by
  intro x; rw [eps4_exp_neg]; simp

theorem beta4 : SLang.β eps4 (PMF.pure ()) (PMF.pure ()) () = ENNReal.ofReal (4/5) := by
  unfold SLang.β
  rw [eps4_exp, eps4_exp_neg]
  have hd : (PMF.pure ()) () / (PMF.pure ()) () = ENNReal.ofReal 1 := by simp
  rw [hd, ← ENNReal.ofReal_sub _ zero_le_one, ← ENNReal.ofReal_sub _ (by norm_num),
    ← ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

theorem apmf_false : (SLang.A_pmf eps4 (PMF.pure ()) (PMF.pure ()) hqp4 ()) false = ENNReal.ofReal (4/5) :=
  beta4

theorem apmf_true : (SLang.A_pmf eps4 (PMF.pure ()) (PMF.pure ()) hqp4 ()) true = ENNReal.ofReal (1/5) := by
  show 1 - SLang.β eps4 (PMF.pure ()) (PMF.pure ()) () = _
  rw [beta4, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]
  norm_num

open SLang

/-- restriction of a PMF to a set containing its support -/
noncomputable def restr {T : Type} (p : PMF T) (s : Set T) (h : Function.support p ⊆ s) : PMF s :=
  ⟨(⇑p) ∘ (↑), (hasSum_subtype_iff_of_support_subset h).2 (PMF.hasSum_coe_one p)⟩

theorem restr_apply {T : Type} (p : PMF T) (s : Set T) (h : Function.support p ⊆ s) (x : s) :
    restr p s h x = p x := rfl

theorem supp_sub {T : Type} (p q : PMF T) (hac : AbsCts p q) : Function.support p ⊆ q.support := by
  intro x hx; rw [PMF.mem_support_iff]; exact fun h => hx (hac x h)

theorem renyi_restr {T : Type} (p q : PMF T) (hac : AbsCts p q) {α : ℝ} (hα : 1 < α) :
    RenyiDivergence_def p q α =
      RenyiDivergence_def (restr p q.support (supp_sub p q hac)) (restr q q.support subset_rfl) α := by
  unfold RenyiDivergence_def
  congr 2
  refine (tsum_subtype_eq_of_support_subset (s := q.support) ?_).symm
  intro x hx
  rw [PMF.mem_support_iff]
  intro hq
  apply hx
  simp only [hq, hac x hq]
  rw [ENNReal.zero_rpow_of_pos (by linarith), zero_mul]

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

open SLang
open scoped Classical

theorem pp_apply {T U V : Type} (nq : SLang.Mechanism T U) (f : U → V) (l : List T) (v : V) :
    (SLang.privPostProcess nq f l).1 v = ∑' a, if v = f a then (nq l).1 a else 0 := by
  simp [privPostProcess, Bind.bind, Pure.pure, probBind, probPure]

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

/-- an SPMF seen as a PMF -/
def toP {U : Type} (x : SLang.SPMF U) : PMF U := ⟨x.1, x.2⟩

/-- the union of the supports of two outputs of a mechanism -/
def pset {T U : Type} (m : SLang.Mechanism T U) (l₁ l₂ : List T) : Set U :=
  PMF.support (toP (m l₁)) ∪ PMF.support (toP (m l₂))

theorem pset_countable {T U : Type} (m : SLang.Mechanism T U) (l₁ l₂ : List T) :
    Countable (pset m l₁ l₂) :=
  ((PMF.support_countable _).union (PMF.support_countable _)).to_subtype

theorem sub1 {T U : Type} (m : SLang.Mechanism T U) (l₁ l₂ : List T) :
    Function.support (toP (m l₁)) ⊆ pset m l₁ l₂ := Set.subset_union_left

theorem sub2 {T U : Type} (m : SLang.Mechanism T U) (l₁ l₂ : List T) :
    Function.support (toP (m l₂)) ⊆ pset m l₁ l₂ := Set.subset_union_right

/-- the mechanism restricted to pset: the output for l₂ at l₂, the output for l₁ elsewhere -/
noncomputable def mresP {T U : Type} (m : SLang.Mechanism T U) (l₁ l₂ : List T) (l : List T) :
    PMF (pset m l₁ l₂) :=
  if l = l₂ then restr (toP (m l₂)) (pset m l₁ l₂) (sub2 m l₁ l₂)
  else restr (toP (m l₁)) (pset m l₁ l₂) (sub1 m l₁ l₂)

theorem mresP_eq {T U : Type} (m : SLang.Mechanism T U) (l₁ l₂ : List T) :
    mresP m l₁ l₂ l₂ = restr (toP (m l₂)) (pset m l₁ l₂) (sub2 m l₁ l₂) := if_pos rfl

theorem mresP_ne {T U : Type} (m : SLang.Mechanism T U) (l₁ l₂ l : List T) (h : l ≠ l₂) :
    mresP m l₁ l₂ l = restr (toP (m l₁)) (pset m l₁ l₂) (sub1 m l₁ l₂) := if_neg h

noncomputable def mres {T U : Type} (m : SLang.Mechanism T U) (l₁ l₂ : List T) :
    SLang.Mechanism T (pset m l₁ l₂) := fun l => ⟨(mresP m l₁ l₂ l).1, (mresP m l₁ l₂ l).2⟩

theorem mres_val1 {T U : Type} (m : SLang.Mechanism T U) (l₁ l₂ : List T) (x : pset m l₁ l₂) :
    (mres m l₁ l₂ l₁).1 x = (m l₁).1 x.1 := by
  show (mresP m l₁ l₂ l₁) x = _
  by_cases h : l₁ = l₂
  · subst h; rw [mresP_eq]; rfl
  · rw [mresP_ne _ _ _ _ h]; rfl

theorem mres_val2 {T U : Type} (m : SLang.Mechanism T U) (l₁ l₂ : List T) (x : pset m l₁ l₂) :
    (mres m l₁ l₂ l₂).1 x = (m l₂).1 x.1 := by
  show (mresP m l₁ l₂ l₂) x = _
  rw [mresP_eq]; rfl

theorem renyi_self {S : Type} [Countable S] (P : PMF S) {α : ℝ} (hα : 1 < α) :
    RenyiDivergence P P α = 0 :=
  (@RenyiDivergence_aux_zero S ⊤ _ _ P P α hα (fun x h => h)).1 rfl

theorem mres_zcdp {T U : Type} (m : SLang.Mechanism T U) (ε : ℝ) (h : SLang.zCDPBound m ε)
    (l₁ l₂ : List T) (hN : Neighbour l₁ l₂) : SLang.zCDPBound (mres m l₁ l₂) ε := by
  have := pset_countable m l₁ l₂
  intro α hα a b _
  show RenyiDivergence (mresP m l₁ l₂ a) (mresP m l₁ l₂ b) α ≤ _
  by_cases ha : a = l₂ <;> by_cases hb : b = l₂
  · rw [ha, hb, renyi_self _ hα]; exact zero_le
  · rw [ha, mresP_eq, mresP_ne _ _ _ _ hb, renyi_restr2 _ _ _ _ _ hα]
    exact h α hα l₂ l₁ (Neighbour_symm _ _ hN)
  · rw [hb, mresP_eq, mresP_ne _ _ _ _ ha, renyi_restr2 _ _ _ _ _ hα]
    exact h α hα l₁ l₂ hN
  · rw [mresP_ne _ _ _ _ ha, mresP_ne _ _ _ _ hb, renyi_self _ hα]; exact zero_le

theorem mres_ac {T U : Type} (m : SLang.Mechanism T U) (h : SLang.ACNeighbour m)
    (l₁ l₂ : List T) (hN : Neighbour l₁ l₂) : SLang.ACNeighbour (mres m l₁ l₂) := by
  intro a b _ x hx
  change (mresP m l₁ l₂ b) x = 0 at hx
  show (mresP m l₁ l₂ a) x = 0
  by_cases ha : a = l₂ <;> by_cases hb : b = l₂
  · rw [ha]; rw [hb] at hx; exact hx
  · rw [ha, mresP_eq]; rw [mresP_ne _ _ _ _ hb] at hx; exact h l₂ l₁ (Neighbour_symm _ _ hN) x.1 hx
  · rw [mresP_ne _ _ _ _ ha]; rw [hb, mresP_eq] at hx; exact h l₁ l₂ hN x.1 hx
  · rw [mresP_ne _ _ _ _ ha]; rw [mresP_ne _ _ _ _ hb] at hx; exact hx

theorem supp_ite1 {T U : Type} (m : SLang.Mechanism T U) (l₁ l₂ : List T) (P : U → Prop) :
    Function.support (fun a => if P a then (m l₁).1 a else 0) ⊆ pset m l₁ l₂ := by
  intro a ha
  apply sub1 m l₁ l₂
  rw [Function.mem_support] at ha ⊢
  intro h0; apply ha
  change (m l₁).1 a = 0 at h0
  simp [h0]

theorem supp_ite2 {T U : Type} (m : SLang.Mechanism T U) (l₁ l₂ : List T) (P : U → Prop) :
    Function.support (fun a => if P a then (m l₂).1 a else 0) ⊆ pset m l₁ l₂ := by
  intro a ha
  apply sub2 m l₁ l₂
  rw [Function.mem_support] at ha ⊢
  intro h0; apply ha
  change (m l₂).1 a = 0 at h0
  simp [h0]

theorem pp_mres1 {T U V : Type} (m : SLang.Mechanism T U) (f : U → V) (l₁ l₂ : List T) :
    SLang.privPostProcess (mres m l₁ l₂) (f ∘ Subtype.val) l₁ = SLang.privPostProcess m f l₁ := by
  apply Subtype.ext; funext v
  rw [pp_apply, pp_apply]
  simp only [Function.comp, mres_val1]
  exact tsum_subtype_eq_of_support_subset (supp_ite1 m l₁ l₂ (fun a => v = f a))

theorem pp_mres2 {T U V : Type} (m : SLang.Mechanism T U) (f : U → V) (l₁ l₂ : List T) :
    SLang.privPostProcess (mres m l₁ l₂) (f ∘ Subtype.val) l₂ = SLang.privPostProcess m f l₂ := by
  apply Subtype.ext; funext v
  rw [pp_apply, pp_apply]
  simp only [Function.comp, mres_val2]
  exact tsum_subtype_eq_of_support_subset (supp_ite2 m l₁ l₂ (fun a => v = f a))

theorem dsum1 {T U : Type} (m : SLang.Mechanism T U) (l₁ l₂ : List T) (S : Set U) :
    ∑' x : pset m l₁ l₂, (if x.1 ∈ S then (mres m l₁ l₂ l₁).1 x else 0) =
      ∑' x : U, if x ∈ S then (m l₁).1 x else 0 := by
  simp only [mres_val1]
  exact tsum_subtype_eq_of_support_subset (supp_ite1 m l₁ l₂ (fun a => a ∈ S))

theorem dsum2 {T U : Type} (m : SLang.Mechanism T U) (l₁ l₂ : List T) (S : Set U) :
    ∑' x : pset m l₁ l₂, (if x.1 ∈ S then (mres m l₁ l₂ l₂).1 x else 0) =
      ∑' x : U, if x ∈ S then (m l₂).1 x else 0 := by
  simp only [mres_val2]
  exact tsum_subtype_eq_of_support_subset (supp_ite2 m l₁ l₂ (fun a => a ∈ S))

open SLang
open scoped Classical

theorem comp_apply {T U V : Type} (nq1 : SLang.Mechanism T U) (nq2 : U → SLang.Mechanism T V)
    (l : List T) (u : U) (v : V) :
    (SLang.privComposeAdaptive nq1 nq2 l).1 (u, v) = (nq1 l).1 u * (nq2 u l).1 v := by
  simp [privComposeAdaptive, Bind.bind, Pure.pure, probBind, probPure]
  exact SLang.compose_sum_rw_adaptive nq1 nq2 u v l

/-- pull a PMF back along an injection whose range contains its support -/
noncomputable def pull {W X : Type} (p : PMF X) (e : W → X) (he : Function.Injective e)
    (hs : Function.support p ⊆ Set.range e) : PMF W :=
  ⟨(⇑p) ∘ e, (he.hasSum_iff (fun x hx => by
      by_contra h; exact hx (hs (Function.mem_support.2 h)))).2 (PMF.hasSum_coe_one p)⟩

theorem renyi_pull {W X : Type} (p q : PMF X) (e : W → X) (he : Function.Injective e)
    (hp : Function.support p ⊆ Set.range e) (hq : Function.support q ⊆ Set.range e)
    {α : ℝ} (hα : 1 < α) :
    RenyiDivergence (pull p e he hp) (pull q e he hq) α = RenyiDivergence p q α := by
  unfold RenyiDivergence RenyiDivergence_def
  congr 3
  refine he.tsum_eq (f := fun x => p x ^ α * q x ^ (1 - α)) ?_
  intro x hx
  by_contra hxs
  apply hx
  have h1 : p x = 0 := by by_contra h; exact hxs (hp (Function.mem_support.2 h))
  have h2 : q x = 0 := by by_contra h; exact hxs (hq (Function.mem_support.2 h))
  simp only [h1]
  rw [ENNReal.zero_rpow_of_pos (by linarith), zero_mul]

open SLang
open scoped Classical

theorem comp_mresU {T U V : Type} (nq1 : SLang.Mechanism T U) (nq2 : U → SLang.Mechanism T V)
    (l₁ l₂ l : List T) (hl : ∀ x : pset nq1 l₁ l₂, (mres nq1 l₁ l₂ l).1 x = (nq1 l).1 x.1)
    (hsub : Function.support (toP (nq1 l)) ⊆ pset nq1 l₁ l₂) :
    toP (SLang.privComposeAdaptive (mres nq1 l₁ l₂) (fun u => nq2 u.1) l) =
      pull (toP (SLang.privComposeAdaptive nq1 nq2 l)) (Prod.map Subtype.val id)
        (Subtype.val_injective.prodMap Function.injective_id) (by
          rintro ⟨u, v⟩ h
          rw [Function.mem_support] at h
          change (SLang.privComposeAdaptive nq1 nq2 l).1 (u, v) ≠ 0 at h
          rw [comp_apply] at h
          have hu : u ∈ pset nq1 l₁ l₂ := hsub (Function.mem_support.2 (left_ne_zero_of_mul h))
          exact ⟨(⟨u, hu⟩, v), rfl⟩) := by
  apply Subtype.ext; funext ⟨u, v⟩
  show (SLang.privComposeAdaptive (mres nq1 l₁ l₂) (fun u => nq2 u.1) l).1 (u, v) =
    (SLang.privComposeAdaptive nq1 nq2 l).1 (u.1, v)
  rw [comp_apply, comp_apply, hl]

open SLang
open scoped Classical

/-- restriction of a mechanism to a set s containing the supports of its outputs at l₁ and l₂ -/
noncomputable def msP {T U : Type} (m : SLang.Mechanism T U) (l₁ l₂ : List T) (s : Set U)
    (h1 : Function.support (toP (m l₁)) ⊆ s) (h2 : Function.support (toP (m l₂)) ⊆ s)
    (l : List T) : PMF s :=
  if l = l₂ then restr (toP (m l₂)) s h2 else restr (toP (m l₁)) s h1

noncomputable def ms {T U : Type} (m : SLang.Mechanism T U) (l₁ l₂ : List T) (s : Set U)
    (h1 : Function.support (toP (m l₁)) ⊆ s) (h2 : Function.support (toP (m l₂)) ⊆ s) :
    SLang.Mechanism T s := fun l => ⟨(msP m l₁ l₂ s h1 h2 l).1, (msP m l₁ l₂ s h1 h2 l).2⟩

theorem ms_val1 {T U : Type} (m : SLang.Mechanism T U) (l₁ l₂ : List T) (s : Set U) h1 h2 (x : s) :
    (ms m l₁ l₂ s h1 h2 l₁).1 x = (m l₁).1 x.1 := by
  show (msP m l₁ l₂ s h1 h2 l₁) x = _
  unfold msP
  by_cases h : l₁ = l₂
  · subst h; rw [if_pos rfl]; rfl
  · rw [if_neg h]; rfl

theorem ms_val2 {T U : Type} (m : SLang.Mechanism T U) (l₁ l₂ : List T) (s : Set U) h1 h2 (x : s) :
    (ms m l₁ l₂ s h1 h2 l₂).1 x = (m l₂).1 x.1 := by
  show (msP m l₁ l₂ s h1 h2 l₂) x = _
  unfold msP; rw [if_pos rfl]; rfl

theorem ms_zcdp {T U : Type} (m : SLang.Mechanism T U) (ε : ℝ) (h : SLang.zCDPBound m ε)
    (l₁ l₂ : List T) (hN : Neighbour l₁ l₂) (s : Set U) [Countable s] h1 h2 :
    SLang.zCDPBound (ms m l₁ l₂ s h1 h2) ε := by
  intro α hα a b _
  show RenyiDivergence (msP m l₁ l₂ s h1 h2 a) (msP m l₁ l₂ s h1 h2 b) α ≤ _
  unfold msP
  by_cases ha : a = l₂ <;> by_cases hb : b = l₂
  · rw [if_pos ha, if_pos hb, renyi_self _ hα]; exact zero_le
  · rw [if_pos ha, if_neg hb, renyi_restr2 _ _ _ _ _ hα]
    exact h α hα l₂ l₁ (Neighbour_symm _ _ hN)
  · rw [if_neg ha, if_pos hb, renyi_restr2 _ _ _ _ _ hα]
    exact h α hα l₁ l₂ hN
  · rw [if_neg ha, if_neg hb, renyi_self _ hα]; exact zero_le

theorem ms_ac {T U : Type} (m : SLang.Mechanism T U) (h : SLang.ACNeighbour m)
    (l₁ l₂ : List T) (hN : Neighbour l₁ l₂) (s : Set U) h1 h2 :
    SLang.ACNeighbour (ms m l₁ l₂ s h1 h2) := by
  intro a b _ x hx
  change (msP m l₁ l₂ s h1 h2 b) x = 0 at hx
  show (msP m l₁ l₂ s h1 h2 a) x = 0
  unfold msP at hx ⊢
  by_cases ha : a = l₂ <;> by_cases hb : b = l₂
  · rw [if_pos ha]; rw [if_pos hb] at hx; exact hx
  · rw [if_pos ha]; rw [if_neg hb] at hx; exact h l₂ l₁ (Neighbour_symm _ _ hN) x.1 hx
  · rw [if_neg ha]; rw [if_pos hb] at hx; exact h l₁ l₂ hN x.1 hx
  · rw [if_neg ha]; rw [if_neg hb] at hx; exact hx

/-- the union over u of the supports of nq2 u at l₁ and l₂ -/
def vset {T U V : Type} (nq2 : U → SLang.Mechanism T V) (l₁ l₂ : List T) : Set V :=
  ⋃ u, pset (nq2 u) l₁ l₂

theorem vsub1 {T U V : Type} (nq2 : U → SLang.Mechanism T V) (l₁ l₂ : List T) (u : U) :
    Function.support (toP (nq2 u l₁)) ⊆ vset nq2 l₁ l₂ :=
  fun _ hx => Set.mem_iUnion.2 ⟨u, sub1 (nq2 u) l₁ l₂ hx⟩

theorem vsub2 {T U V : Type} (nq2 : U → SLang.Mechanism T V) (l₁ l₂ : List T) (u : U) :
    Function.support (toP (nq2 u l₂)) ⊆ vset nq2 l₁ l₂ :=
  fun _ hx => Set.mem_iUnion.2 ⟨u, sub2 (nq2 u) l₁ l₂ hx⟩

theorem comp_msV {T U V : Type} (nq1 : SLang.Mechanism T U) (nq2 : U → SLang.Mechanism T V)
    (l₁ l₂ l : List T)
    (hl : ∀ u (x : vset nq2 l₁ l₂),
      (ms (nq2 u) l₁ l₂ (vset nq2 l₁ l₂) (vsub1 nq2 l₁ l₂ u) (vsub2 nq2 l₁ l₂ u) l).1 x = (nq2 u l).1 x.1)
    (hsub : ∀ u, Function.support (toP (nq2 u l)) ⊆ vset nq2 l₁ l₂) :
    toP (SLang.privComposeAdaptive nq1
        (fun u => ms (nq2 u) l₁ l₂ (vset nq2 l₁ l₂) (vsub1 nq2 l₁ l₂ u) (vsub2 nq2 l₁ l₂ u)) l) =
      pull (toP (SLang.privComposeAdaptive nq1 nq2 l)) (Prod.map id Subtype.val)
        (Function.injective_id.prodMap Subtype.val_injective) (by
          rintro ⟨u, v⟩ h
          rw [Function.mem_support] at h
          change (SLang.privComposeAdaptive nq1 nq2 l).1 (u, v) ≠ 0 at h
          rw [comp_apply] at h
          have hv : v ∈ vset nq2 l₁ l₂ := hsub u (Function.mem_support.2 (right_ne_zero_of_mul h))
          exact ⟨(u, ⟨v, hv⟩), rfl⟩) := by
  apply Subtype.ext; funext ⟨u, v⟩
  show (SLang.privComposeAdaptive nq1
      (fun u => ms (nq2 u) l₁ l₂ (vset nq2 l₁ l₂) (vsub1 nq2 l₁ l₂ u) (vsub2 nq2 l₁ l₂ u)) l).1 (u, v) =
    (SLang.privComposeAdaptive nq1 nq2 l).1 (u, v.1)
  rw [comp_apply, comp_apply, hl]

open SLang

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

theorem term4 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ENNReal.ofReal a ^ (4:ℝ) * ENNReal.ofReal b ^ (1 - 4 : ℝ) = ENNReal.ofReal (a ^ 4 / b ^ 3) := by
  rw [ENNReal.ofReal_rpow_of_pos ha, ENNReal.ofReal_rpow_of_pos hb, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast, show (1:ℝ) - ((4:ℕ):ℝ) = -((3:ℕ):ℝ) by norm_num,
    Real.rpow_neg hb.le, Real.rpow_natCast, div_eq_mul_inv]

theorem exp_one_lt_four : Real.exp 1 < 4 := by
  have h1 : 1 - 1/2 < Real.exp (-(1/2)) := by
    have := Real.add_one_lt_exp (x := -(1/2)) (by norm_num); linarith
  have h2 : Real.exp (1/2) < 2 := by
    rw [Real.exp_neg] at h1
    have hp := Real.exp_pos (1/2)
    rw [lt_inv_comm₀ (by norm_num) hp] at h1
    linarith
  have : Real.exp 1 = Real.exp (1/2) * Real.exp (1/2) := by rw [← Real.exp_add]; norm_num
  rw [this]; nlinarith [Real.exp_pos (1/2)]

end Probe2

-- `Renyi_Jensen_ENNReal_converse` idx 9: necessary (T = Bool, p = pure true, q = uniform, α = 2: AbsCts holds, p ≠ q)
theorem p2_1 : ¬ drop0% Renyi_Jensen_ENNReal_converse 9 := fun h =>
  absurd (@h Bool _ _ _ (PMF.pure true) (PMF.uniformOfFintype Bool) 2 (by norm_num)
    (fun x hx => by simp at hx)) (by
      intro he
      have := congrArg (fun p : PMF Bool => p false) he
      simp at this
      exact absurd this.symm (by simp))

-- `RenyiDivergence_def_nonneg` idx 3: removable (restrict p, q to the countable support of q (AbsCts), apply the theorem there with the discrete σ-algebra; the tsum is unchanged)
theorem p2_2 : drop% RenyiDivergence_def_nonneg 3 := by
  intro T inst msc p q hac α hα
  have : Countable q.support := q.support_countable.to_subtype
  rw [Probe2.renyi_restr p q hac hα]
  exact @RenyiDivergence_def_nonneg q.support ⊤ _ _ _ _ (Probe2.ac_restr p q hac) α hα

-- `RenyiDivergence_def_eq_0_iff` idx 3: removable (same countable-support restriction as idx 3 of RenyiDivergence_def_nonneg; restriction preserves and reflects p = q under AbsCts)
theorem p2_3 : drop% RenyiDivergence_def_eq_0_iff 3 := by
  intro T inst msc p q α hα hac
  have : Countable q.support := q.support_countable.to_subtype
  rw [Probe2.renyi_restr p q hac hα, ← Probe2.restr_eq_iff p q hac]
  exact @RenyiDivergence_def_eq_0_iff q.support ⊤ _ _ _ _ α hα (Probe2.ac_restr p q hac)

-- `RenyiDivergence_def_eq_0_iff` idx 8: removable (without AbsCts some q x = 0 < p x, the sum is ⊤, the divergence is ⊤ ≠ 0 and p ≠ q, so both sides of the iff are false)
theorem p2_4 : drop% RenyiDivergence_def_eq_0_iff 8 := by
  intro T inst msc cnt p q α hα
  by_cases hac : AbsCts p q
  · exact RenyiDivergence_def_eq_0_iff p q hα hac
  · obtain ⟨x, hqx, hpx⟩ : ∃ x, q x = 0 ∧ p x ≠ 0 := by simpa [AbsCts] using hac
    have hpq : p ≠ q := fun e => hpx (e ▸ hqx)
    have hpos : p x ^ α ≠ 0 :=
      (ENNReal.rpow_pos (pos_iff_ne_zero.2 hpx) (PMF.apply_ne_top p x)).ne'
    have hsum : ∑' x, p x ^ α * q x ^ (1 - α) = ⊤ := ENNReal.tsum_eq_top_of_eq_top
      ⟨x, by rw [hqx, ENNReal.zero_rpow_of_neg (by linarith)]; exact ENNReal.mul_top hpos⟩
    simp only [RenyiDivergence_def, hsum, hpq, iff_false]
    rw [show ENNReal.elog ⊤ = ⊤ from rfl, EReal.mul_top_of_pos]
    · exact EReal.top_ne_zero
    · exact_mod_cast inv_pos.2 (sub_pos.2 hα)

-- `RenyiDivergence_def_log_sum_nonneg` idx 2: removable (conclusion does not mention the σ-algebra: instantiate the theorem at the discrete σ-algebra ⊤)
theorem p2_5 : drop% RenyiDivergence_def_log_sum_nonneg 2 := by
  intro T inst cnt p q hac α hα
  exact @RenyiDivergence_def_log_sum_nonneg T ⊤ _ _ p q hac α hα

-- `RenyiDivergence_def_log_sum_nonneg` idx 8: necessary (α = 1/2, p = pure true, q = uniform on Bool: sum = (1/2)^(1/2) < 1, elog negative)
theorem p2_6 : ¬ drop0% RenyiDivergence_def_log_sum_nonneg 8 := fun h =>
  absurd (@h Bool _ _ _ (PMF.pure true) (PMF.uniformOfFintype Bool) (fun x hx => by simp at hx) (1/2)) (by
    rw [tsum_bool]
    simp
    have hr : (0:ℝ) < (2⁻¹:ℝ) ^ (1 - (2⁻¹:ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    have e1 : (2⁻¹ : ENNReal) ^ (1 - (2⁻¹:ℝ)) = ENNReal.ofReal ((2⁻¹:ℝ) ^ (1 - (2⁻¹:ℝ))) := by
      rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by norm_num), ENNReal.ofReal_inv_of_pos two_pos]
      simp
    rw [e1, ENNReal.elog_of_pos_real hr]
    have := Real.log_neg hr (Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num))
    exact_mod_cast this)

-- `RenyiDivergence_aux_zero` idx 2: removable (conclusion does not mention the σ-algebra: instantiate at ⊤)
theorem p2_7 : drop% RenyiDivergence_aux_zero 2 := by
  intro T inst cnt p q α hα hac
  exact @RenyiDivergence_aux_zero T ⊤ _ _ p q α hα hac

-- `SLang.sup_lemma` idx 2: necessary (U = Empty, s = 0: eexp(0 * ⊥) = 1 but the empty ENNReal supremum is 0)
theorem p2_8 : ¬ drop0% SLang.sup_lemma 2 := fun h =>
  absurd (@h Empty 0 EReal.zero_lt_top (fun _ => 0)) (by simp [ENNReal.eexp_zero])

-- `SLang.privComposeAdaptive_zCDPBound` idx 5: removable (zCDPBound does not mention the σ-algebra: instantiate at ⊤ on U)
theorem p2_9 : drop% SLang.privComposeAdaptive_zCDPBound 5 := by
  intro T U V HU HUm HUc
  exact @SLang.privComposeAdaptive_zCDPBound T U V HU ⊤ _ HUc

-- `SLang.privComposeAdaptive_zCDPBound` idx 6: removable (restrict nq1 to the countable union of the supports of nq1 l₁, nq1 l₂ (output for l₂ at l₂, for l₁ elsewhere), apply the theorem there, pull the composition back along the injection; Rényi divergence unchanged)
theorem p2_10 : drop% SLang.privComposeAdaptive_zCDPBound 6 := by
  intro T U V HU HUm HUd instV mscV cV nq1 nq2 ε₁ ε₂ h1 h2 ac1 ac2 b1 b2 α hα l₁ l₂ hN
  have := Probe2.pset_countable nq1 l₁ l₂
  have hinh : Inhabited (Probe2.pset nq1 l₁ l₂) :=
    ⟨⟨(PMF.support_nonempty (Probe2.toP (nq1 l₁))).some,
      Or.inl (PMF.support_nonempty (Probe2.toP (nq1 l₁))).some_mem⟩⟩
  have key := @SLang.privComposeAdaptive_zCDPBound T (Probe2.pset nq1 l₁ l₂) V hinh ⊤ _ _ instV mscV cV
    (Probe2.mres nq1 l₁ l₂) (fun u => nq2 u.1) ε₁ ε₂ h1 h2 (Probe2.mres_ac nq1 ac1 l₁ l₂ hN)
    (fun u => ac2 u.1) (Probe2.mres_zcdp nq1 ε₁ b1 l₁ l₂ hN) (fun u => b2 u.1) α hα l₁ l₂ hN
  change RenyiDivergence
    (Probe2.toP (SLang.privComposeAdaptive (Probe2.mres nq1 l₁ l₂) (fun u => nq2 u.1) l₁))
    (Probe2.toP (SLang.privComposeAdaptive (Probe2.mres nq1 l₁ l₂) (fun u => nq2 u.1) l₂)) α
    ≤ ENNReal.ofReal ((ε₁ + ε₂) * α) at key
  rw [Probe2.comp_mresU nq1 nq2 l₁ l₂ l₁ (Probe2.mres_val1 nq1 l₁ l₂) (Probe2.sub1 nq1 l₁ l₂),
    Probe2.comp_mresU nq1 nq2 l₁ l₂ l₂ (Probe2.mres_val2 nq1 l₁ l₂) (Probe2.sub2 nq1 l₁ l₂)] at key
  exact (Probe2.renyi_pull _ _ _ _ _ _ hα).symm.trans_le key

-- `SLang.privComposeAdaptive_zCDPBound` idx 9: removable (restrict every nq2 u to the countable union over u of the supports at l₁, l₂, apply the theorem there, pull back along the injection U × S → U × V)
theorem p2_11 : drop% SLang.privComposeAdaptive_zCDPBound 9 := by
  intro T U V HU HUm HUd HUc instV mscV nq1 nq2 ε₁ ε₂ h1 h2 ac1 ac2 b1 b2 α hα l₁ l₂ hN
  have hc : Countable (Probe2.vset nq2 l₁ l₂) :=
    (Set.countable_iUnion (fun u => (PMF.support_countable _).union (PMF.support_countable _))).to_subtype
  have key := @SLang.privComposeAdaptive_zCDPBound T U (Probe2.vset nq2 l₁ l₂) HU HUm HUd HUc ⊤ _ hc
    nq1 (fun u => Probe2.ms (nq2 u) l₁ l₂ _ (Probe2.vsub1 nq2 l₁ l₂ u) (Probe2.vsub2 nq2 l₁ l₂ u))
    ε₁ ε₂ h1 h2 ac1 (fun u => Probe2.ms_ac (nq2 u) (ac2 u) l₁ l₂ hN _ _ _) b1
    (fun u => Probe2.ms_zcdp (nq2 u) ε₂ (b2 u) l₁ l₂ hN _ _ _) α hα l₁ l₂ hN
  change RenyiDivergence
    (Probe2.toP (SLang.privComposeAdaptive nq1 (fun u => Probe2.ms (nq2 u) l₁ l₂ _
      (Probe2.vsub1 nq2 l₁ l₂ u) (Probe2.vsub2 nq2 l₁ l₂ u)) l₁))
    (Probe2.toP (SLang.privComposeAdaptive nq1 (fun u => Probe2.ms (nq2 u) l₁ l₂ _
      (Probe2.vsub1 nq2 l₁ l₂ u) (Probe2.vsub2 nq2 l₁ l₂ u)) l₂)) α
    ≤ ENNReal.ofReal ((ε₁ + ε₂) * α) at key
  rw [Probe2.comp_msV nq1 nq2 l₁ l₂ l₁ (fun u => Probe2.ms_val1 (nq2 u) l₁ l₂ _ _ _)
      (Probe2.vsub1 nq2 l₁ l₂),
    Probe2.comp_msV nq1 nq2 l₁ l₂ l₂ (fun u => Probe2.ms_val2 (nq2 u) l₁ l₂ _ _ _)
      (Probe2.vsub2 nq2 l₁ l₂)] at key
  exact (Probe2.renyi_pull _ _ _ _ _ _ hα).symm.trans_le key

-- `SLang.privComposeAdaptive_AC` idx 5: necessary (nq1 [] = pure true, nq1 _ = pure false, nq2 = pure (): composition not AC on [] ~ [()])
theorem p2_12 : ¬ drop0% SLang.privComposeAdaptive_AC 5 := fun h =>
  absurd (h Probe2.nq12 (fun _ _ => SPMF_pure ()) (fun u l1 l2 _ x hx => hx) [] [()]
    (Neighbour.Addition (a := []) (b := []) (n := ()) rfl rfl) (true, ())) (by
    simp [privComposeAdaptive, Probe2.nq12, Bind.bind, Pure.pure]
    exact ⟨(by show probPure (false, ()) (true, ()) = 0; simp [probPure]),
      (by show ¬ probPure (true, ()) (true, ()) = 0; simp [probPure])⟩)

-- `sg_sum_pos'` idx 2: necessary (σ = 0: Gaussian terms are 1, the ℤ-tsum is 0, ratio 0, 0^1 = 0)
theorem p2_13 : ¬ drop0% sg_sum_pos' 2 := fun h =>
  absurd (@h 0 0 0 1) (by simp [gauss_term_ℝ])

-- `SG_Renyi_simplify` idx 2: removable (σ = 0: both sides are 0 (tsum over ℤ of 1 is 0, 0^α·0^(1-α) = 0))
theorem p2_14 : drop% SG_Renyi_simplify 2 := by
  intro x σ μ ν α
  by_cases hσ : σ = 0
  · subst hσ
    rcases eq_or_ne α 0 with rfl | hα
    · simp [gauss_term_ℝ]
    · simp [gauss_term_ℝ, Real.zero_rpow hα]
  · exact SG_Renyi_simplify hσ μ ν α

-- `Renyi_Gauss_summable` idx 1: removable (σ = 0: discrete_gaussian is 0, the summand 0^α·0^(1-α) is 0, summable)
theorem p2_15 : drop% Renyi_Gauss_summable 1 := by
  intro σ μ ν α
  by_cases hσ : σ = 0
  · subst hσ
    have h0 : ∀ a : ℝ, (0:ℝ) ^ a * (0:ℝ) ^ (1 - a) = 0 := by
      intro a
      rcases eq_or_ne a 0 with rfl | ha
      · simp
      · simp [Real.zero_rpow ha]
    simp [discrete_gaussian, gauss_term_ℝ, h0]
  · exact Renyi_Gauss_summable hσ μ ν α

-- `SLang.HαSpecial_algebraic` idx 4: necessary (ε = 1, S = 0, D = 1)
theorem p2_16 : ¬ drop0% SLang.HαSpecial_algebraic 4 := fun h =>
  absurd (@h 1 0 1 one_ne_zero) (by norm_num)

-- `SLang.ApproximateDP_α_gt_one` idx 3: necessary (ε = 1, δ = 0: log(1/0) = 0, so 1 < 1 fails)
theorem p2_17 : ¬ drop0% SLang.ApproximateDP_α_gt_one 3 := fun h =>
  absurd (h 1 one_pos 0 (by norm_num)) (by norm_num)

-- `SLang.ApproximateDP_renyi_tsum_le` idx 10: removable (0 < ↑α - 1 in EReal follows from 1 < α)
theorem p2_18 : drop% SLang.ApproximateDP_renyi_tsum_le 10 := by
  intro U cnt m1 m2 h1 h2 ε hε α hα
  refine SLang.ApproximateDP_renyi_tsum_le m1 m2 h1 h2 ε hε α hα ?_
  rw [← EReal.coe_one, ← EReal.coe_sub]
  exact_mod_cast sub_pos.2 hα

-- `SLang.ApproximateDP_of_zCDP_pos` idx 2: removable (restrict the mechanism to the countable union of the supports of m l₁, m l₂ (still zCDP and AC), apply the theorem there; the DP' sums are unchanged)
theorem p2_19 : drop% SLang.ApproximateDP_of_zCDP_pos 2 := by
  intro T U m ε hε h hac δ hδ
  unfold SLang.DP'
  intro l₁ l₂ hN S
  have := Probe2.pset_countable m l₁ l₂
  have key := @SLang.ApproximateDP_of_zCDP_pos T (Probe2.pset m l₁ l₂) _ (Probe2.mres m l₁ l₂) ε hε
    (Probe2.mres_zcdp m _ h l₁ l₂ hN) (Probe2.mres_ac m hac l₁ l₂ hN) δ hδ l₁ l₂ hN (Subtype.val ⁻¹' S)
  refine le_of_eq_of_le ?_ (key.trans_eq ?_)
  · exact (Probe2.dsum1 m l₁ l₂ S).symm
  · congr 2
    exact Probe2.dsum2 m l₁ l₂ S

-- `SLang.β_ne_top` idx 5: necessary (ε = 0, p = pure true, q = pure false, x = false: β = 1/0 = ⊤)
theorem p2_20 : ¬ drop0% SLang.β_ne_top 5 := fun h =>
  absurd (@h Bool 0 (PMF.pure true) (PMF.pure false) false) (by simp [SLang.β])

-- `SLang.A_expectation` idx 7: removable (AbsCts follows from the bound p x / q x ≤ exp ε (p x / 0 = ⊤ when p x ≠ 0))
theorem p2_21 : drop% SLang.A_expectation 7 := by
  intro U ε p q hε Hqp Hpq x
  refine SLang.A_expectation ε p q hε Hqp Hpq ?_ x
  intro y hqy
  by_contra hp
  have := Hpq y
  rw [hqy, ENNReal.div_zero hp] at this
  exact absurd (this.trans_lt ENNReal.ofReal_lt_top) (lt_irrefl _)

-- `SLang.A_jensen_real` idx 6: necessary (α = 1/2, ε = log 4, p = q = pure (): LHS 1^(1/2) = 1, RHS 4/5)
theorem p2_22 : ¬ drop0% SLang.A_jensen_real 6 := fun h => by
  have h1 := @h Unit Probe2.eps4 (PMF.pure ()) (PMF.pure ()) Probe2.hqp4 (1/2) ()
  simp only [tsum_bool, Probe2.apmf_false, Probe2.apmf_true, SLang.A_val, Probe2.eps4_exp,
    Probe2.eps4_exp_neg, ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 4/5),
    ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1/5), ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 4),
    ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 4⁻¹)] at h1
  have e1 : (4:ℝ)⁻¹ * (4/5) + 4 * (1/5) = 1 := by norm_num
  have e2 : (4:ℝ) ^ (1/2 : ℝ) = 2 := by
    rw [show (4:ℝ) = 2 ^ (2:ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
  have e3 : (4⁻¹:ℝ) ^ (1/2 : ℝ) = 2⁻¹ := by
    rw [Real.inv_rpow (by norm_num), e2]
  rw [e1, Real.one_rpow, e2, e3] at h1
  norm_num at h1

-- `SLang.A_jensen` idx 4: removable (ε = 0: A_val = 1, both sides equal 1 (A_pmf sums to 1))
theorem p2_23 : drop% SLang.A_jensen 4 := by
  intro U ε p q Hqp α hα x
  by_cases hε : ε = 0
  · subst hε
    have hA : ∀ b, SLang.A_val 0 b = 1 := by intro b; cases b <;> simp [SLang.A_val]
    simp only [hA, one_mul, ENNReal.one_rpow, PMF.tsum_coe, le_refl]
  · exact SLang.A_jensen ε p q (pos_iff_ne_zero.2 hε) Hqp hα x

-- `SLang.B_eval_false_closed_form` idx 5: necessary (ε = 1, Bval = 0: closed form (e-1)/(e-e⁻¹) ≠ 0)
theorem p2_24 : ¬ drop0% SLang.B_eval_false_closed_form 5 := fun h =>
  absurd (h 1 one_pos 0 (by simp) (by simp)) (by
    intro e
    rw [eq_comm, ENNReal.div_eq_zero_iff] at e
    rcases e with e | e
    · rw [tsub_eq_zero_iff_le] at e
      have : (1:ℝ) + 1 < Real.exp 1 := Real.add_one_lt_exp one_ne_zero
      simp at e
      linarith
    · exact absurd e (ENNReal.sub_ne_top ENNReal.ofReal_ne_top))

-- `SLang.lemma_step_1` idx 2: necessary (x = y = 0: LHS 0/0 = 0, RHS (1+0)/(1-0) = 1)
theorem p2_25 : ¬ drop0% SLang.lemma_step_1 2 := fun h =>
  absurd (h 0 0) (by simp [SLang.t])

-- `SLang.lemma_step_3_deriv_nonneg` idx 4: removable (the function is odd, so its derivative is even (deriv_comp_neg, no differentiability needed): use the theorem at -z)
theorem p2_26 : drop% SLang.lemma_step_3_deriv_nonneg 4 := by
  intro x z hx2 hx0
  rcases le_total 0 z with hz | hz
  · exact SLang.lemma_step_3_deriv_nonneg x z hx2 hx0 hz
  · have h2 := SLang.lemma_step_3_deriv_nonneg x (-z) hx2 hx0 (by linarith)
    set g : ℝ → ℝ := fun z => Real.tanh (x * z / 4) - Real.tanh (x / 2) * Real.tanh (z / 2) with hg
    have hodd : (fun z => g (-z)) = -g := by
      funext z; simp only [hg, Pi.neg_apply, mul_neg, neg_div, Real.tanh_neg]; ring
    have := congrArg (fun F => deriv F (-z)) hodd
    simp only [deriv_comp_neg, deriv.neg, neg_neg] at this
    rw [neg_inj] at this
    rw [this]; exact h2

-- `SLang.ofDP_bound_large_εα` idx 9: necessary (ε = log 2, α = 4, lists [] and [(),(),(),(),()]; mass of true (1/2)^(min len 5 + 1) is pure log 2-DP, but the Rényi divergence (1/3)·log S with S > 4096 exceeds 2(log 2)^2)
theorem p2_27 : ¬ drop0% SLang.ofDP_bound_large_εα 9 := fun h => by
  have hl2 : 1/2 < Real.log 2 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have h1 : 1 - 1/2 < Real.exp (-(1/2)) := by
      have := Real.add_one_lt_exp (x := -(1/2)) (by norm_num); linarith
    rw [Real.exp_neg] at h1
    rw [lt_inv_comm₀ (by norm_num) (Real.exp_pos _)] at h1
    linarith
  have hl2' : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (x := 2) (by norm_num) (by norm_num); linarith
  have h1 := @h Unit Bool Probe2.q27 Probe2.eps2 Probe2.q27_dp 4 (by norm_num) [] [(), (), (), (), ()]
    (by show Real.log 2 * 4 > 2; linarith)
  unfold RenyiDivergence RenyiDivergence_def at h1
  rw [tsum_bool] at h1
  change ENNReal.ofEReal (((4:ℝ) - 1)⁻¹ * ENNReal.elog
      (ENNReal.ofReal (Probe2.w 0 false) ^ (4:ℝ) * ENNReal.ofReal (Probe2.w 5 false) ^ (1 - 4 : ℝ) +
       ENNReal.ofReal (Probe2.w 0 true) ^ (4:ℝ) * ENNReal.ofReal (Probe2.w 5 true) ^ (1 - 4 : ℝ)))
    ≤ _ at h1
  rw [Probe2.term4 _ _ (Probe2.w_pos _ _) (Probe2.w_pos _ _),
    Probe2.term4 _ _ (Probe2.w_pos _ _) (Probe2.w_pos _ _),
    ← ENNReal.ofReal_add (div_pos (pow_pos (Probe2.w_pos _ _) _) (pow_pos (Probe2.w_pos _ _) _)).le
      (div_pos (pow_pos (Probe2.w_pos _ _) _) (pow_pos (Probe2.w_pos _ _) _)).le] at h1
  set S := Probe2.w 0 false ^ 4 / Probe2.w 5 false ^ 3 + Probe2.w 0 true ^ 4 / Probe2.w 5 true ^ 3 with hS
  have hS1 : 4096 < S := by
    rw [hS]; simp only [Probe2.w]; norm_num
  have hSpos : 0 < S := by linarith
  rw [ENNReal.elog_of_pos_real hSpos, ← EReal.coe_mul, ENNReal.ofEReal_real] at h1
  have hpos : 0 ≤ 1/2 * (Probe2.eps2 : ℝ) ^ 2 * 4 := by positivity
  rw [ENNReal.ofReal_le_ofReal_iff hpos] at h1
  have he : (Probe2.eps2 : ℝ) = Real.log 2 := rfl
  rw [he] at h1
  have h6 : 6 < Real.log S := by
    rw [Real.lt_log_iff_exp_lt hSpos]
    have e6 : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e6]
    have := pow_lt_pow_left₀ Probe2.exp_one_lt_four (Real.exp_pos 1).le (by norm_num : (6:ℕ) ≠ 0)
    linarith
  have hl0 : 0 < Real.log 2 := by linarith
  norm_num at h1
  nlinarith

-- `SLang.ofDP_bound_large_εα` idx 10: removable (sibling SLang.ofDP_bound gives the bound for every α > 1 from PureDP)
theorem p2_28 : drop% SLang.ofDP_bound_large_εα 10 := by
  intro T U q' ε H α hα l1 l2 hN
  have := SLang.ofDP_bound ε q' H α hα l1 l2 hN
  convert this using 2

-- `SLang.ofDP_bound_ratio_inv` idx 5: necessary (p = q = pure true, ε = 0, x = false: 0/0 = 0 < 1)
theorem p2_29 : ¬ drop0% SLang.ofDP_bound_ratio_inv 5 := fun h =>
  absurd (@h Bool (PMF.pure true) (PMF.pure true) 0 false (by simp)) (by simp)

-- `SLang.δpmf_conv` idx 7 (dependent): necessary (nq = ⊤ on Unit: the tsum is ⊤)
theorem p2_30 : ¬ indep0% SLang.δpmf_conv 7 := fun h =>
  have hs : ∑' (i : ↑{n : Unit | () = id n}), (fun _ => (⊤ : ENNReal)) i.1 = ⊤ :=
    ENNReal.tsum_eq_top_of_eq_top ⟨⟨(), rfl⟩, rfl⟩
  absurd (@h Unit Unit id (fun _ => ⊤) () ⟨(), rfl⟩ (by rw [hs]; exact top_ne_zero)) (by
    simp only [ne_eq, not_not]; exact hs)

-- `SLang.δpmf_conv'` idx 6 (dependent): necessary (nq = ⊤ on Unit: the tsum is ⊤)
theorem p2_31 : ¬ indep0% SLang.δpmf_conv' 6 := fun h =>
  have hs : ∑' (i : ↑{n : Unit | () = id n}), (fun _ => (⊤ : ENNReal)) i.1 = ⊤ :=
    ENNReal.tsum_eq_top_of_eq_top ⟨⟨(), rfl⟩, rfl⟩
  absurd (@h Unit Unit (fun _ => ⊤) id () (by rw [hs]; exact top_ne_zero)) (by
    simp only [ne_eq, not_not]; exact hs)

-- `SLang.privPostPocess_DP_pre_reduct` idx 5: removable (conclusion does not mention the σ-algebra: instantiate at ⊤ (discrete))
theorem p2_32 : drop% SLang.privPostPocess_DP_pre_reduct 5 := by
  intro T V U m2 cnt inh
  exact @SLang.privPostPocess_DP_pre_reduct T V U ⊤ cnt _ inh

-- `SLang.privPostPocess_DP_pre_reduct` idx 10: necessary (α = 1/2, U = Bool, V = Unit, f constant, nq [] = (9/25,16/25), nq [()] = (16/25,9/25): LHS 1, RHS 24/25)
theorem p2_33 : ¬ drop0% SLang.privPostPocess_DP_pre_reduct 10 := fun h => by
  have h1 := @h Unit Unit Bool _ _ _ _ Probe2.sf (fun _ => ()) (1/2) [] [()] (Probe2.sf_sum _)
    (Probe2.sf_sum _) (fun x hx => absurd hx (Probe2.sf_ne _ x)) (Probe2.sf_ne _)
    (Neighbour.Addition (a := []) (b := []) (n := ()) rfl rfl)
  have hs : ∑ a, Probe2.sf [] a = 1 := by simpa [tsum_fintype] using (Probe2.sf_sum []).tsum_eq
  have hs' : ∑ a, Probe2.sf [()] a = 1 := by simpa [tsum_fintype] using (Probe2.sf_sum [()]).tsum_eq
  simp only [if_true, tsum_fintype, Finset.univ_unique, Finset.sum_singleton] at h1
  rw [hs, hs', Fintype.sum_bool] at h1
  have e2 : (1:ℝ) - 1/2 = 1/2 := by norm_num
  simp only [e2, ENNReal.one_rpow, Probe2.sf] at h1
  simp only [Probe2.sq_rpow_half, reduceCtorEq, if_true, if_false] at h1
  simp at h1
  rw [Probe2.sq_rpow_inv_two] at h1
  have e3 : (3 * 5⁻¹ * (4 * 5⁻¹) + 4 * 5⁻¹ * (3 * 5⁻¹) : ENNReal) = (5⁻¹)^2 * 24 := by ring
  have e4 : (1 : ENNReal) = (5⁻¹)^2 * 25 := by
    rw [show (5⁻¹ : ENNReal)^2 * 25 = (5 * 5⁻¹)^2 by ring, Probe2.five_inv, one_pow]
  have hlt : (5⁻¹ : ENNReal)^2 * 24 < (5⁻¹)^2 * 25 :=
    ENNReal.mul_lt_mul_right (by simp) (by simp) (by norm_num)
  rw [e3] at h1
  exact absurd (h1.trans_lt hlt) (by rw [← e4]; exact lt_irrefl _)

-- `SLang.privPostProcess_zCDPBound` idx 8: necessary (ε = 0, f = id, nq [] uniform, nq _ = (3/4,1/4) on Bool: divergence 0 would force equality)
theorem p2_34 : ¬ drop0% SLang.privPostProcess_zCDPBound 8 := fun h => by
  have hAC : SLang.ACNeighbour Probe2.mech := fun l1 l2 _ x hx => absurd hx (Probe2.mf_ne l2 x)
  have h1 := @h Unit Bool Bool _ _ _ Probe2.mech 0 id hAC 2 (by norm_num) [] [()]
    (Neighbour.Addition (a := []) (b := []) (n := ()) rfl rfl)
  simp only [zero_mul, ENNReal.ofReal_zero, nonpos_iff_eq_zero] at h1
  have he := (RenyiDivergence_aux_zero _ _ (by norm_num : (1:ℝ) < 2) ?_).2 h1
  · have := congrArg (fun p => p.1 true) he
    simp only [Probe2.pp_val] at this
    simp [Probe2.mf] at this
  · intro x hx
    change (SLang.privPostProcess Probe2.mech id [()]).1 x = 0 at hx
    rw [Probe2.pp_val] at hx; exact absurd hx (Probe2.mf_ne _ x)

-- `SLang.privPostProcess_zCDP` idx 4: removable (AC of post-processing is direct; the bound follows from privPostProcess_zCDPBound applied to the mechanism restricted to the countable union of the supports at l₁, l₂)
theorem p2_35 : drop% SLang.privPostProcess_zCDP 4 := by
  intro T U V inst disc f nq ε h
  obtain ⟨hac, hb⟩ := h
  refine ⟨?_, ?_⟩
  · intro l₁ l₂ hN v hv
    change (SLang.privPostProcess nq f l₂).1 v = 0 at hv
    show (SLang.privPostProcess nq f l₁).1 v = 0
    rw [Probe2.pp_apply, ENNReal.tsum_eq_zero] at hv ⊢
    intro a
    have := hv a
    split_ifs at this ⊢ with hva
    · exact hac l₁ l₂ hN a this
    · rfl
  · intro α hα l₁ l₂ hN
    have := Probe2.pset_countable nq l₁ l₂
    have key := @SLang.privPostProcess_zCDPBound T (Probe2.pset nq l₁ l₂) V ⊤ _ _
      (Probe2.mres nq l₁ l₂) ε (Probe2.mres_zcdp nq ε hb l₁ l₂ hN) (f ∘ Subtype.val)
      (Probe2.mres_ac nq hac l₁ l₂ hN) α hα l₁ l₂ hN
    rw [Probe2.pp_mres1, Probe2.pp_mres2] at key
    exact key

-- `SLang.probUniformByteUpperBits_eval_support` idx 2: necessary (i = 0, x = 1: probability 0 (eval_zero) but RHS 2^8/256 = 1)
theorem p2_36 : ¬ drop0% SLang.probUniformByteUpperBits_eval_support 2 := fun h =>
  absurd (@h 0 1) (by
    rw [SLang.probUniformByteUpperBits_eval_zero (by simp), eq_comm, ENNReal.div_eq_zero_iff]
    simp [UInt8.size])

-- `SLang.BernoulliExpNegSampleUnitAux_monotone_counter` idx 7: necessary (num = 0, den = 1, fuel = 2, st = (true,1), n = 2: the loop reaches (false,2) with probability 1)
theorem p2_37 : ¬ drop0% SLang.BernoulliExpNegSampleUnitAux_monotone_counter 7 := fun h =>
  absurd (h 0 1 2 (true, 1) 2 (by simp) (by simp)) (by
    simp [probWhileCut, probWhileFunctional, BernoulliExpNegSampleUnitLoop, BernoulliSample_apply]
    rfl)

-- `SLang.mass'_series_converges'_even` idx 1: necessary (γ = ⊤: mass' 2 ⊤ = ⊤)
theorem p2_38 : ¬ drop0% SLang.mass'_series_converges'_even 1 := fun h =>
  absurd (h ⊤) (by
    simp only [ne_eq, not_not]
    exact ENNReal.tsum_eq_top_of_eq_top ⟨1, by simp [SLang.mass', ENNReal.top_mul]⟩)

-- `SLang.probGeometric_apply_Geo` idx 1: necessary (t = 0, x = 1: LHS 0, RHS Geo 1 0 = 1)
theorem p2_39 : ¬ drop0% SLang.probGeometric_apply_Geo 1 := fun h =>
  absurd (h (fun _ => 0) (by simp) 1) (by
    rw [SLang.probGeometric_apply]; simp [SLang.Geo])

-- `SLang.probGeometric_apply_Geo` idx 2: removable (t true = 1 forces t false = 0, both sides 0 (probGeometric_apply))
theorem p2_40 : drop% SLang.probGeometric_apply_Geo 2 := by
  intro t h1 x
  by_cases ht : t true < 1
  · exact SLang.probGeometric_apply_Geo t h1 ht x
  · have ht1 : t true = 1 := le_antisymm (h1 ▸ le_add_self) (not_lt.1 ht)
    have hf : t false = 0 := by
      rw [ht1] at h1
      have := congrArg (· - 1) h1
      simpa [ENNReal.add_sub_cancel_right] using this
    rw [SLang.probGeometric_apply]
    simp [SLang.Geo, ht1, hf]

-- `SLang.geo_div_geo` idx 3: removable (p ≥ 1: 1 - p = 0 and 1 - p^n = 0, both sides 0)
theorem p2_41 : drop% SLang.geo_div_geo 3 := by
  intro k n p hn
  by_cases hp : p < 1
  · exact SLang.geo_div_geo k n p hp hn
  · push_neg at hp
    have h0 : 1 - p = 0 := tsub_eq_zero_of_le hp
    have h1 : 1 - p ^ n = 0 := tsub_eq_zero_of_le (one_le_pow₀ hp)
    simp [SLang.Geo, h0, h1, Bind.bind, Pure.pure]

-- `SLang.geo_div_geo` idx 4: necessary (p = 0, n = 0, k = 0: v/0 = 0 gives LHS 1, RHS Geo 0 0 = 0)
theorem p2_42 : ¬ drop0% SLang.geo_div_geo 4 := fun h =>
  absurd (h 0 0 0 zero_lt_one) (by
    simp [SLang.Geo, Bind.bind, Pure.pure])

-- `SLang.UniformSample_support_Sum` idx 2: necessary (n = 1, m = 2: sum 1, RHS 2)
theorem p2_43 : ¬ drop0% SLang.UniformSample_support_Sum 2 := fun h =>
  absurd (h 1 2) (by
    rw [Finset.sum_range_succ, Finset.sum_range_one, SLang.UniformSample_apply 1 0 (by decide),
      SLang.UniformSample_apply_out 1 1 (by decide)]
    norm_num)

-- `gauss_convergence_nat_pos` idx 1: necessary (σ = 0: constant 1 is not summable over ℕ)
theorem p2_44 : ¬ drop0% gauss_convergence_nat_pos 1 := fun h =>
  absurd (@h 0 0) (by simp [gauss_term_ℝ, summable_const_iff])

-- `shifted_gauss_sum` idx 1: removable (σ = 0: both tsums are tsums of 1 over ℤ, equal)
theorem p2_45 : drop% shifted_gauss_sum 1 := by
  intro σ μ k
  by_cases hσ : σ = 0
  · subst hσ; simp [gauss_term_ℝ]
  · exact shifted_gauss_sum hσ μ k

-- `ENNReal.ofEReal_mul_nonneg` idx 2: removable (w < 0, z ≥ 0: w*z ≤ 0, so both sides are 0)
theorem p2_46 : drop% ENNReal.ofEReal_mul_nonneg 2 := by
  intro w z hz
  rcases le_or_gt 0 w with hw | hw
  · exact ENNReal.ofEReal_mul_nonneg hw hz
  · have h1 : w * z ≤ 0 := EReal.mul_nonpos_iff.mpr (Or.inr ⟨hw.le, hz⟩)
    rw [(ENNReal.ofEReal_eq_zero_iff _).mp h1, (ENNReal.ofEReal_eq_zero_iff _).mp hw.le, zero_mul]

-- `ENNReal.ofEReal_nonneg_scal_l` idx 2: necessary (r = 0, w = ⊥)
theorem p2_47 : ¬ drop0% ENNReal.ofEReal_nonneg_scal_l 2 := fun h =>
  absurd (@h 0 ⊥ (by simp)) (by simp)

-- `ENNReal.ofReal_injective_nonneg` idx 3: necessary (r = 0, s = -1)
theorem p2_48 : ¬ drop0% ENNReal.ofReal_injective_nonneg 3 := fun h =>
  absurd (@h 0 (-1) le_rfl (by simp)) (by norm_num)

-- `ENNReal.ofReal_injective_nonneg` idx 4: necessary (r = 0, s = 1)
theorem p2_49 : ¬ drop0% ENNReal.ofReal_injective_nonneg 4 := fun h =>
  absurd (@h 0 1 le_rfl zero_le_one) (by norm_num)

-- `ENNReal.ereal_le_smul_left` idx 4: removable (s = ⊤: ⊤ * w is monotone in w (⊥, 0, ⊤ by sign))
theorem p2_50 : drop% ENNReal.ereal_le_smul_left 4 := by
  intro w z s hs hwz
  rcases (le_top : s ≤ ⊤).lt_or_eq with h | rfl
  · exact ENNReal.ereal_le_smul_left s hs h hwz
  · rcases lt_trichotomy w 0 with hw | rfl | hw
    · rw [EReal.top_mul_of_neg hw]; exact bot_le
    · rcases lt_trichotomy z 0 with hz | rfl | hz
      · exact absurd (hwz.trans_lt hz) (lt_irrefl _)
      · exact le_rfl
      · rw [EReal.top_mul_of_pos hz]; exact le_top
    · rw [EReal.top_mul_of_pos (hw.trans_le hwz)]; exact le_top

