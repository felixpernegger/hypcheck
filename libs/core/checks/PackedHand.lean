import Lean

/-!
Hand pass `Packed` (hand12): 81 unresolved hypotheses of `Init.Grind.Ring.Packed` (67),
`Init.Grind.Ring.Envelope` (13) and `Init.Grind.Ring.OfScientific` (1). Each declaration proves
`¬ T'` (`drop0% T i`, universes set to `0`) or `T'` (`drop% T i`, universes kept).

57 necessary, 19 removable, 0 independent, 5 left unresolved.

Reusable models (namespace `PackedHand`):
* `X0` (x₀ packed in base 2) with `ctx2` (xᵢ ↦ i + 2 over Int): digit overflow, x₀·x₀ packs to x₁ (3 ≠ 4);
  refutes every degree/overflow bound (`D₁ + D₂ < B`, `Deg`, `dsum v ≤ D₁`, `D * k < B`, `degB_k * k < B`).
* `P0`, `P1`, `P0p1` (x₀, x₁, x₀ + 1 as Poly), `c01` (x₀ = 0, x₁ = 1), `T0` (one zero leaf, `T0_zero`),
  `Tov` (an overflowing leaf): base `B = 1` packs every variable to code 1, so x₀ and x₁ collide.
* `NI`: ℕ ∪ {∞} with n + ∞ = ∞, a semiring with `IsCharP NI 0` and no additive cancellation;
  its ring envelope is trivial.
* `NL` (Nat with `<` always false) and `NT` (Nat with `≤` always true, usual `<`, an `OrderedRing`
  with `ExistsAddOfLT`): order instances that are not `LawfulOrderLT`.

Removable: `1 < B` throughout the packed-monomial lemmas. For `B ≤ 1`, `dsum` is `0` and `monDenote`
is `1`, so `dsum_add`, `monDenote_add`, `dsum_div_le` hold without it, and `dsum_mul_pow`,
`monDenote_mul_pow` too because `k < B` forces `k = 0`. The library proofs of the `_k_spec` lemmas
use `1 < B` only through these, except in the variable cases, where `1 ≤ D < B` supplies it. The
helpers `*_noB` (namespace `Lean.Grind.CommRing`) are the library proofs with these substitutions.

Run with the lean4 repo's stage1 binary (`runs/hand12/lean.sh checks/PackedHand.lean`).
-/
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

open Lean Meta Elab Term in
/-- `drop% T i`: `T` with its (non-dependent) Prop binder `i` dropped, read off the library. -/
elab "drop% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

open Lean Meta Elab Term in
/-- `indep% T i`: `∀ indep, Hᵢ` for the dependent Prop binder `i` of `T` (all independent binders). -/
elab "indep% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
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

open Lean Meta Elab Term in
/-- `drop0% T i`: `drop% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "drop0% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => levelZero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body


attribute [local instance] Lean.Grind.Semiring.natCast Lean.Grind.Ring.intCast

open Std
open Lean.Grind
open AddCommMonoid AddCommGroup NatModule IntModule
open Semiring hiding add_zero add_comm add_assoc
open Ring hiding sub_eq_add_neg
open CommSemiring
namespace Lean.Grind.CommRing

/-! Copies of the library proofs with `1 < B` dropped (helpers for the removable verdicts). For
`B ≤ 1`, `dsum` is `0` and `monDenote` is `1`; the variable cases get `1 < B` from `1 ≤ D < B`. -/

theorem PPoly.dsum_of_not {B : Nat} (hB : ¬ 1 < B) (v : Nat) : PPoly.dsum B v = 0 := by
  rw [PPoly.dsum]; simp [hB]

theorem PPoly.monDenote_of_not {α} [Semiring α] (ctx : Nat → α) {B : Nat} (hB : ¬ 1 < B) (i v : Nat) :
    PPoly.monDenote ctx B i v = 1 := by
  rw [PPoly.monDenote]; simp [hB]

theorem PPoly.dsum_div_le_noB {B : Nat} (v : Nat) : dsum B (v / B) ≤ dsum B v := by
  by_cases hB : 1 < B
  · exact PPoly.dsum_div_le hB v
  · rw [dsum_of_not hB, dsum_of_not hB]; exact Nat.le_refl _

theorem PPoly.dsum_add_noB {B : Nat} (v₁ v₂ : Nat) (h : dsum B v₁ + dsum B v₂ < B) :
    dsum B (v₁ + v₂) = dsum B v₁ + dsum B v₂ := by
  by_cases hB : 1 < B
  · exact PPoly.dsum_add hB v₁ v₂ h
  · simp [dsum_of_not hB]

theorem PPoly.monDenote_add_noB {B : Nat} {α} [CommSemiring α] (ctx : Nat → α) (i v₁ v₂ : Nat)
    (h : dsum B v₁ + dsum B v₂ < B) :
    monDenote ctx B i (v₁ + v₂) = monDenote ctx B i v₁ * monDenote ctx B i v₂ := by
  by_cases hB : 1 < B
  · exact PPoly.monDenote_add ctx hB i v₁ v₂ h
  · rw [monDenote_of_not ctx hB, monDenote_of_not ctx hB, monDenote_of_not ctx hB, Semiring.mul_one]

theorem PPoly.dsum_mul_pow_noB {B : Nat} (x k : Nat) (hk : k < B) : dsum B (k * B ^ x) = k := by
  by_cases hB : 1 < B
  · exact PPoly.dsum_mul_pow hB x k hk
  · have : k = 0 := by omega
    subst this; exact dsum_of_not hB _

theorem PPoly.monDenote_mul_pow_noB {B : Nat} {α} [Semiring α] (ctx : Nat → α) (i x k : Nat) (hk : k < B) :
    monDenote ctx B i (k * B ^ x) = ctx (i + x) ^ k := by
  by_cases hB : 1 < B
  · exact PPoly.monDenote_mul_pow ctx hB i x k hk
  · have : k = 0 := by omega
    subst this; rw [monDenote_of_not ctx hB, Semiring.pow_zero]

theorem PPoly.mulMon_k_spec_noB {α} [CommRing α] (ctx : Nat → α) (B D₁ D₂ : Nat) (k : Int) (d v : Nat)
    (hv : dsum B v ≤ D₁) (hD : D₁ + D₂ < B) (p : PPoly) (hp : p.Deg B D₂) :
    (p.mulMon_k k d v).denote ctx B = k * monDenote ctx B 0 v * p.denote ctx B ∧ (p.mulMon_k k d v).Deg B (D₁ + D₂) := by
  induction p with
  | num k' =>
    unfold mulMon_k
    dsimp only
    cases h : Int.beqZero_k k'
    · refine ⟨?_, ⟨by omega, trivial⟩⟩
      show ((Int.mul_k k k' : Int) : α) * _ + ((Int.ofNat 0 : Int) : α) = _
      rw [Int.mul_k_eq]
      show ((k * k' : Int) : α) * _ + ((0 : Int) : α) = _
      rw [intCast_zero, add_zero, intCast_mul]
      show _ = _ * ((k' : Int) : α)
      simp only [mul_assoc, mul_comm, mul_left_comm]
    · simp at h; subst h
      refine ⟨?_, trivial⟩
      show ((Int.ofNat 0 : Int) : α) = _ * ((0 : Int) : α)
      simp [intCast_zero, mul_zero]
  | add k' d' v' p ih =>
    obtain ⟨ih₁, ih₂⟩ := ih hp.2
    have hs := dsum_add_noB (B := B) v v' (by have := hp.1; omega)
    refine ⟨?_, ⟨by rw [Nat.add_eq, hs]; have := hp.1; omega, ih₂⟩⟩
    show ((Int.mul_k k k' : Int) : α) * monDenote ctx B 0 (Nat.add v v') + (p.mulMon_k k d v).denote ctx B = _
    rw [ih₁, Int.mul_k_eq, Nat.add_eq, monDenote_add_noB (B := B) ctx 0 v v' (by have := hp.1; omega)]
    show ((k * k' : Int) : α) * _ + _ = _ * ((k' : α) * _ + denote ctx B p)
    rw [intCast_mul, left_distrib]
    simp only [mul_assoc, mul_left_comm]

theorem PPoly.mulTerms_k_spec_noB {α} [CommRing α] (ctx : Nat → α) (B D₁ D₂ : Nat) (hD : D₁ + D₂ < B)
    (p₁ p₂ : PPoly) (h₁ : p₁.Deg B D₁) (h₂ : p₂.Deg B D₂) :
    denoteList ctx B (mulTerms_k p₁ p₂) = p₁.denote ctx B * p₂.denote ctx B ∧ DegList B (D₁ + D₂) (mulTerms_k p₁ p₂) := by
  induction p₁ with
  | num k =>
    have := mulConst_k_spec ctx B D₂ k p₂
    refine ⟨?_, fun q hq => ?_⟩
    · show (p₂.mulConst_k k).denote ctx B + 0 = _
      rw [add_zero, this.1]; rfl
    · simp only [mulTerms_k, List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq; exact Deg.mono (by omega) _ (this.2 h₂)
  | add k d v p ih =>
    have hm := mulMon_k_spec_noB ctx B D₁ D₂ k d v h₁.1 hD p₂ h₂
    have ih := ih h₁.2
    refine ⟨?_, fun q hq => ?_⟩
    · show (p₂.mulMon_k k d v).denote ctx B + denoteList ctx B (mulTerms_k p p₂) = _
      rw [hm.1, ih.1]
      show _ = ((k : α) * _ + denote ctx B p) * _
      rw [right_distrib]
    · simp only [mulTerms_k, List.mem_cons] at hq
      rcases hq with hq | hq
      · subst hq; exact hm.2
      · exact ih.2 q hq

theorem PPoly.mulB_k_spec_noB {α} [CommRing α] (ctx : Nat → α) (B D₁ D₂ : Nat) (hD : D₁ + D₂ < B)
    (p₁ p₂ : PPoly) (h₁ : p₁.Deg B D₁) (h₂ : p₂.Deg B D₂) :
    (mulB_k p₁ p₂).denote ctx B = p₁.denote ctx B * p₂.denote ctx B ∧ (mulB_k p₁ p₂).Deg B (D₁ + D₂) := by
  cases p₁ with
  | num k =>
    have := mulConst_k_spec ctx B D₂ k p₂
    exact ⟨this.1, Deg.mono (by omega) _ (this.2 h₂)⟩
  | add k₁ d₁ v₁ q₁ =>
    cases p₂ with
    | num k =>
      have := mulConst_k_spec ctx B D₁ k (.add k₁ d₁ v₁ q₁)
      refine ⟨?_, Deg.mono (by omega) _ (this.2 h₁)⟩
      show ((PPoly.add k₁ d₁ v₁ q₁).mulConst_k k).denote ctx B = _
      rw [this.1, mul_comm]; rfl
    | add k₂ d₂ v₂ q₂ =>
      rw [show mulB_k (.add k₁ d₁ v₁ q₁) (.add k₂ d₂ v₂ q₂) = Bool.rec (Bool.rec (sumB_k (mulTerms_k (.add k₁ d₁ v₁ q₁) (.add k₂ d₂ v₂ q₂)))
        (mulByMon_k (.add k₂ d₂ v₂ q₂) (.add k₁ d₁ v₁ q₁)) (isMon_k (.add k₂ d₂ v₂ q₂)))
        (mulByMon_k (.add k₁ d₁ v₁ q₁) (.add k₂ d₂ v₂ q₂)) (isMon_k (.add k₁ d₁ v₁ q₁)) from rfl]
      cases hm₁ : isMon_k (.add k₁ d₁ v₁ q₁)
      · cases hm₂ : isMon_k (.add k₂ d₂ v₂ q₂)
        · have ht := mulTerms_k_spec_noB ctx B D₁ D₂ hD _ _ h₁ h₂
          have hs := sumB_k_spec ctx B (D₁ + D₂) (mulTerms_k (.add k₁ d₁ v₁ q₁) (.add k₂ d₂ v₂ q₂))
          exact ⟨by rw [hs.1, ht.1], hs.2 ht.2⟩
        · obtain ⟨k, d, v, e⟩ := isMon_k_eq _ hm₂
          rw [e] at h₂ ⊢
          have := mulMon_k_spec_noB ctx B D₂ D₁ k d v h₂.1 (by omega) _ h₁
          refine ⟨?_, by rw [Nat.add_comm]; exact this.2⟩
          show ((PPoly.add k₁ d₁ v₁ q₁).mulMon_k k d v).denote ctx B = _
          rw [this.1]
          show _ = _ * ((k : α) * _ + ((0 : Int) : α))
          rw [intCast_zero, add_zero, mul_comm]
      · obtain ⟨k, d, v, e⟩ := isMon_k_eq _ hm₁
        rw [e] at h₁ ⊢
        have := mulMon_k_spec_noB ctx B D₁ D₂ k d v h₁.1 hD _ h₂
        refine ⟨?_, this.2⟩
        show ((PPoly.add k₂ d₂ v₂ q₂).mulMon_k k d v).denote ctx B = _
        rw [this.1]
        show _ = ((k : α) * _ + ((0 : Int) : α)) * _
        rw [intCast_zero, add_zero]

theorem PPoly.powB_k_spec_noB {α} [CommRing α] (ctx : Nat → α) (B D : Nat) (p : PPoly) (k : Nat)
    (hp : p.Deg B D) (hD : D * k < B) :
    (powB_k p k).denote ctx B = p.denote ctx B ^ k ∧ (powB_k p k).Deg B (D * k) := by
  induction k with
  | zero => exact ⟨by show ((Int.ofNat 1 : Int) : α) = _; rw [pow_zero]; exact intCast_one, trivial⟩
  | succ k ih =>
    rw [show powB_k p (k + 1) = Bool.rec (p.mulB_k (powB_k p k)) p (Nat.beq k 0) from rfl]
    cases hk : Nat.beq k 0
    · have ih := ih (by rw [Nat.mul_succ] at hD; omega)
      have := mulB_k_spec_noB ctx B D (D * k) (by rw [Nat.mul_succ] at hD; omega) p (powB_k p k) hp ih.2
      refine ⟨?_, by rw [Nat.mul_succ, Nat.add_comm]; exact this.2⟩
      show (p.mulB_k (powB_k p k)).denote ctx B = _
      rw [this.1, ih.1, pow_succ, mul_comm]
    · have : k = 0 := Nat.eq_of_beq_eq_true hk
      subst this
      exact ⟨by rw [pow_one], by rw [Nat.mul_one]; exact hp⟩

theorem Expr.powPP_k_spec_noB {α} [CommRing α] (ctx : Nat → α) (B : Nat) (a : Expr) (k : Nat) (p : PPoly)
    (hp : 0 < k → p.denote ctx B = a.denoteF ctx ∧ p.Deg B a.degB_k) (hk : a.degB_k * k < B) :
    (a.powPP_k B k p).denote ctx B = a.denoteF ctx ^ k ∧ (a.powPP_k B k p).Deg B (a.degB_k * k) := by
  unfold powPP_k
  cases hk0 : Nat.beq k 0
  · have hgen : (p.powB_k k).denote ctx B = a.denoteF ctx ^ k ∧ (p.powB_k k).Deg B (a.degB_k * k) := by
      have hp := hp (by cases k; simp at hk0; omega)
      have := PPoly.powB_k_spec_noB ctx B a.degB_k p k hp.2 hk
      rw [hp.1] at this; exact this
    dsimp only
    cases a with
    | num n =>
      refine ⟨?_, trivial⟩
      show ((Int.pow_k n k : Int) : α) = denoteInt n ^ k
      rw [Int.pow_k_eq, intCast_pow, denoteInt_eq]
    | natCast n =>
      refine ⟨?_, trivial⟩
      show (((n ^ k : Nat) : Int) : α) = (NatCast.natCast n : α) ^ k
      rw [intCast_natCast]; exact Semiring.natCast_pow (α := α) n k
    | intCast n =>
      refine ⟨?_, trivial⟩
      show ((Int.pow_k n k : Int) : α) = (IntCast.intCast n : α) ^ k
      rw [Int.pow_k_eq, intCast_pow]
    | var x =>
      have hkB : k < B := by have : Expr.degB_k (.var x) * k = 1 * k := rfl; omega
      refine ⟨?_, ⟨?_, trivial⟩⟩
      · show ((Int.ofNat 1 : Int) : α) * PPoly.monDenote ctx B 0 (Nat.mul k (Nat.pow B x)) + ((Int.ofNat 0 : Int) : α) = ctx x ^ k
        rw [show Nat.mul k (Nat.pow B x) = k * B ^ x from rfl, PPoly.monDenote_mul_pow_noB (B := B) ctx 0 x k hkB, Nat.zero_add]
        show ((1 : Int) : α) * _ + ((0 : Int) : α) = _
        rw [intCast_one, one_mul, intCast_zero, add_zero]
      · rw [show Nat.mul k (Nat.pow B x) = k * B ^ x from rfl, PPoly.dsum_mul_pow_noB (B := B) x k hkB]
        show k ≤ 1 * k; omega
    | neg _ => exact hgen
    | add _ _ => exact hgen
    | sub _ _ => exact hgen
    | mul _ _ => exact hgen
    | pow _ _ => exact hgen
  · have : k = 0 := Nat.eq_of_beq_eq_true hk0
    subst this
    exact ⟨by show ((Int.ofNat 1 : Int) : α) = _; rw [pow_zero]; exact intCast_one, trivial⟩

theorem Expr.toPPAcc_k_spec_noB {α} [CommRing α] (ctx : Nat → α) (B : Nat) (e : Expr) :
    ∀ (D : Nat) (acc : PPoly), e.degB_k ≤ D → D < B → acc.Deg B D →
      (e.toPPAcc_k B acc).denote ctx B = e.denoteF ctx + acc.denote ctx B ∧ (e.toPPAcc_k B acc).Deg B D := by
  induction e with
  | num k =>
    intro D acc _ _ hacc
    have := PPoly.addConst_k_spec ctx B D acc k
    refine ⟨?_, this.2 hacc⟩
    show (acc.addConst_k k).denote ctx B = denoteInt k + _
    rw [this.1, denoteInt_eq, add_comm]
  | natCast k =>
    intro D acc _ _ hacc
    have := PPoly.addConst_k_spec ctx B D acc (Int.ofNat k)
    refine ⟨?_, this.2 hacc⟩
    show (acc.addConst_k (Int.ofNat k)).denote ctx B = NatCast.natCast k + _
    rw [this.1, add_comm]
    exact congrArg (· + _) (intCast_natCast k)
  | intCast k =>
    intro D acc _ _ hacc
    have := PPoly.addConst_k_spec ctx B D acc k
    refine ⟨?_, this.2 hacc⟩
    show (acc.addConst_k k).denote ctx B = IntCast.intCast k + _
    rw [this.1, add_comm]
  | var x =>
    intro D acc hd hDB hacc
    have hB : 1 < B := by have : (Expr.var x).degB_k = 1 := rfl; omega
    have hx : PPoly.dsum B (Nat.pow B x) = 1 := by
      have := PPoly.dsum_mul_pow hB x 1 hB; rwa [Nat.one_mul] at this
    have := PPoly.combine_k_spec ctx B D (.add (Int.ofNat 1) 1 (Nat.pow B x) (.num (Int.ofNat 0))) acc
    refine ⟨?_, this.2 ⟨by rw [hx]; exact hd, trivial⟩ hacc⟩
    rw [toPPAcc_k_var, this.1]
    show _ = ctx x + _
    show ((Int.ofNat 1 : Int) : α) * PPoly.monDenote ctx B 0 (Nat.pow B x) + ((Int.ofNat 0 : Int) : α) + _ = _
    have hm := PPoly.monDenote_mul_pow ctx hB 0 x 1 hB
    rw [Nat.one_mul] at hm
    rw [show Nat.pow B x = B ^ x from rfl, hm, Nat.zero_add, pow_one]
    show ((1 : Int) : α) * _ + ((0 : Int) : α) + _ = _
    rw [intCast_one, one_mul, intCast_zero, add_zero]
  | neg a ih =>
    intro D acc hd hD hacc
    have ha := ih D (.num (Int.ofNat 0)) hd hD trivial
    have hn := PPoly.mulConst_k_spec ctx B D (Int.negSucc 0) (a.toPPAcc_k B (.num (Int.ofNat 0)))
    have hc := PPoly.combine_k_spec ctx B D ((a.toPPAcc_k B (.num (Int.ofNat 0))).mulConst_k (Int.negSucc 0)) acc
    refine ⟨?_, by rw [toPPAcc_k_neg]; exact hc.2 (hn.2 ha.2) hacc⟩
    rw [toPPAcc_k_neg, hc.1, hn.1, ha.1, PPoly.denote_num_zero, add_zero]
    show ((-1 : Int) : α) * _ + _ = - a.denoteF ctx + _
    rw [intCast_neg_one, ← neg_eq_neg_one_mul]
  | add a b iha ihb =>
    intro D acc hd hD hacc
    have hm := Expr.le_max_k a.degB_k b.degB_k
    have hb := ihb D acc (Nat.le_trans hm.2 hd) hD hacc
    have ha := iha D (b.toPPAcc_k B acc) (Nat.le_trans hm.1 hd) hD hb.2
    refine ⟨?_, by rw [toPPAcc_k_add]; exact ha.2⟩
    rw [toPPAcc_k_add, ha.1, hb.1]
    show _ = a.denoteF ctx + b.denoteF ctx + _
    rw [add_assoc]
  | sub a b iha ihb =>
    intro D acc hd hD hacc
    have hm := Expr.le_max_k a.degB_k b.degB_k
    have hb := ihb D (.num (Int.ofNat 0)) (Nat.le_trans hm.2 hd) hD trivial
    have hn := PPoly.mulConst_k_spec ctx B D (Int.negSucc 0) (b.toPPAcc_k B (.num (Int.ofNat 0)))
    have hc := PPoly.combine_k_spec ctx B D ((b.toPPAcc_k B (.num (Int.ofNat 0))).mulConst_k (Int.negSucc 0)) acc
    have ha := iha D _ (Nat.le_trans hm.1 hd) hD (hc.2 (hn.2 hb.2) hacc)
    refine ⟨?_, by rw [toPPAcc_k_sub]; exact ha.2⟩
    rw [toPPAcc_k_sub, ha.1, hc.1, hn.1, hb.1, PPoly.denote_num_zero, add_zero]
    show _ + (((-1 : Int) : α) * _ + _) = a.denoteF ctx - b.denoteF ctx + _
    rw [sub_eq_add_neg, add_assoc]
    rw [intCast_neg_one, ← neg_eq_neg_one_mul]
  | mul a b iha ihb =>
    intro D acc hd hD hacc
    have ha := iha a.degB_k (.num (Int.ofNat 0)) (Nat.le_refl _) (by have : a.degB_k + b.degB_k ≤ D := hd; omega) trivial
    have hb := ihb b.degB_k (.num (Int.ofNat 0)) (Nat.le_refl _) (by have : a.degB_k + b.degB_k ≤ D := hd; omega) trivial
    have hp := PPoly.mulB_k_spec_noB ctx B a.degB_k b.degB_k (by have : a.degB_k + b.degB_k ≤ D := hd; omega) _ _ ha.2 hb.2
    have hc := PPoly.combine_k_spec ctx B D (PPoly.mulB_k (a.toPPAcc_k B (.num (Int.ofNat 0))) (b.toPPAcc_k B (.num (Int.ofNat 0)))) acc
    refine ⟨?_, by rw [toPPAcc_k_mul]; exact hc.2 (PPoly.Deg.mono hd _ hp.2) hacc⟩
    rw [toPPAcc_k_mul, hc.1, hp.1, ha.1, hb.1, PPoly.denote_num_zero, add_zero, add_zero]
  | pow a k ih =>
    intro D acc hd hD hacc
    have hd' : a.degB_k * k ≤ D := hd
    have hp := powPP_k_spec_noB ctx B a k (a.toPPAcc_k B (.num (Int.ofNat 0))) (fun hk => by
      have := ih a.degB_k (.num (Int.ofNat 0)) (Nat.le_refl _)
        (by have : a.degB_k ≤ a.degB_k * k := Nat.le_mul_of_pos_right _ hk; omega) trivial
      rw [PPoly.denote_num_zero, add_zero] at this; exact this) (by omega)
    have hc := PPoly.combine_k_spec ctx B D (a.powPP_k B k (a.toPPAcc_k B (.num (Int.ofNat 0)))) acc
    rw [toPPAcc_k_pow]
    exact ⟨by rw [hc.1, hp.1], hc.2 (PPoly.Deg.mono hd' _ hp.2) hacc⟩

theorem Expr.denote_toPP_k_noB {α} [CommRing α] (ctx : Nat → α) (B : Nat) (e : Expr) (he : e.degB_k < B) :
    (e.toPP_k B).denote ctx B = e.denoteF ctx := by
  have := toPPAcc_k_spec_noB ctx B e e.degB_k (.num (Int.ofNat 0)) (Nat.le_refl _) he trivial
  rw [Expr.toPP_k, this.1, PPoly.denote_num_zero, add_zero]

theorem Expr.sumsPP_k_spec_noB {α} [CommRing α] (ctx : Nat → α) (B : Nat) (e : Expr) :
    ∀ (D : Nat) (s : Bool) (acc : List PPoly), e.degB_k ≤ D → D < B → PPoly.DegList B D acc →
      PPoly.denoteList ctx B (e.sumsPP_k B s acc) = Bool.rec (e.denoteF ctx) (- e.denoteF ctx) s + PPoly.denoteList ctx B acc ∧
      PPoly.DegList B D (e.sumsPP_k B s acc) := by
  induction e with
  | num k =>
    intro D s acc _ _ hacc
    have := PPoly.signB_k_spec ctx B D (.num k) s
    refine ⟨?_, PPoly.DegList.cons (this.2 trivial) hacc⟩
    show (PPoly.signB_k (.num k) s).denote ctx B + _ = _
    rw [this.1]
    show Bool.rec (motive := fun _ => α) (k : α) (-(k : α)) s + _ = Bool.rec (motive := fun _ => α) (denoteInt k) (-denoteInt k) s + _
    rw [denoteInt_eq]; rfl
  | natCast k =>
    intro D s acc _ _ hacc
    have := PPoly.signB_k_spec ctx B D (.num (Int.ofNat k)) s
    refine ⟨?_, PPoly.DegList.cons (this.2 trivial) hacc⟩
    show (PPoly.signB_k (.num (Int.ofNat k)) s).denote ctx B + _ = _
    rw [this.1]
    show Bool.rec (motive := fun _ => α) (((k : Int) : α)) (-((k : Int) : α)) s + _ =
      Bool.rec (motive := fun _ => α) (NatCast.natCast k) (- NatCast.natCast k) s + _
    rw [intCast_natCast]; rfl
  | intCast k =>
    intro D s acc _ _ hacc
    have := PPoly.signB_k_spec ctx B D (.num k) s
    refine ⟨?_, PPoly.DegList.cons (this.2 trivial) hacc⟩
    show (PPoly.signB_k (.num k) s).denote ctx B + _ = _
    rw [this.1]; rfl
  | var x =>
    intro D s acc hd hDB hacc
    have hB : 1 < B := by have : (Expr.var x).degB_k = 1 := rfl; omega
    have hx : PPoly.dsum B (Nat.pow B x) = 1 := by
      have := PPoly.dsum_mul_pow hB x 1 hB; rwa [Nat.one_mul] at this
    have := PPoly.signB_k_spec ctx B D (.add (Int.ofNat 1) 1 (Nat.pow B x) (.num (Int.ofNat 0))) s
    refine ⟨?_, PPoly.DegList.cons (this.2 ⟨by rw [hx]; exact hd, trivial⟩) hacc⟩
    show (PPoly.signB_k _ s).denote ctx B + _ = Bool.rec (motive := fun _ => α) (ctx x) (- ctx x) s + _
    rw [this.1]
    have hm := PPoly.monDenote_mul_pow ctx hB 0 x 1 hB
    rw [Nat.one_mul] at hm
    have : (PPoly.add (Int.ofNat 1) 1 (Nat.pow B x) (.num (Int.ofNat 0))).denote ctx B = ctx x := by
      show ((Int.ofNat 1 : Int) : α) * PPoly.monDenote ctx B 0 (Nat.pow B x) + ((Int.ofNat 0 : Int) : α) = _
      rw [show Nat.pow B x = B ^ x from rfl, hm, Nat.zero_add, pow_one]
      show ((1 : Int) : α) * _ + ((0 : Int) : α) = _
      rw [intCast_one, one_mul, intCast_zero, add_zero]
    rw [this]; rfl
  | neg a ih =>
    intro D s acc hd hD hacc
    have := ih D (Bool.rec true false s) acc hd hD hacc
    refine ⟨?_, this.2⟩
    show PPoly.denoteList ctx B (a.sumsPP_k B (Bool.rec true false s) acc) = Bool.rec (motive := fun _ => α) (- a.denoteF ctx) (- - a.denoteF ctx) s + _
    rw [this.1]
    cases s
    · rfl
    · show a.denoteF ctx + _ = - - a.denoteF ctx + _; rw [neg_neg]
  | add a b iha ihb =>
    intro D s acc hd hD hacc
    have hm := Expr.le_max_k a.degB_k b.degB_k
    have hb := ihb D s acc (Nat.le_trans hm.2 hd) hD hacc
    have ha := iha D s _ (Nat.le_trans hm.1 hd) hD hb.2
    refine ⟨?_, ha.2⟩
    show PPoly.denoteList ctx B (a.sumsPP_k B s (b.sumsPP_k B s acc)) =
      Bool.rec (motive := fun _ => α) (a.denoteF ctx + b.denoteF ctx) (- (a.denoteF ctx + b.denoteF ctx)) s + _
    rw [ha.1, hb.1]
    cases s
    · show _ = _ + _ + _; rw [add_assoc]
    · show -a.denoteF ctx + (-b.denoteF ctx + _) = _; rw [neg_add, add_assoc]
  | sub a b iha ihb =>
    intro D s acc hd hD hacc
    have hm := Expr.le_max_k a.degB_k b.degB_k
    have hb := ihb D (Bool.rec true false s) acc (Nat.le_trans hm.2 hd) hD hacc
    have ha := iha D s _ (Nat.le_trans hm.1 hd) hD hb.2
    refine ⟨?_, ha.2⟩
    show PPoly.denoteList ctx B (a.sumsPP_k B s (b.sumsPP_k B (Bool.rec true false s) acc)) =
      Bool.rec (motive := fun _ => α) (a.denoteF ctx - b.denoteF ctx) (- (a.denoteF ctx - b.denoteF ctx)) s + _
    rw [ha.1, hb.1]
    cases s
    · show a.denoteF ctx + (- b.denoteF ctx + _) = _ - _ + _; rw [sub_eq_add_neg, add_assoc]
    · show _ = -(a.denoteF ctx - b.denoteF ctx) + _
      rw [neg_sub, sub_eq_add_neg]
      show -a.denoteF ctx + (b.denoteF ctx + _) = _
      rw [add_assoc, add_left_comm]
  | mul a b iha ihb =>
    intro D s acc hd hD hacc
    have hd' : a.degB_k + b.degB_k ≤ D := hd
    have ha := iha a.degB_k false [] (Nat.le_refl _) (by omega) (fun _ h => by cases h)
    have hb := ihb b.degB_k false [] (Nat.le_refl _) (by omega) (fun _ h => by cases h)
    have hsa := PPoly.sumB_k_spec ctx B a.degB_k (a.sumsPP_k B false [])
    have hsb := PPoly.sumB_k_spec ctx B b.degB_k (b.sumsPP_k B false [])
    have hp := PPoly.mulB_k_spec_noB ctx B a.degB_k b.degB_k (by omega) _ _ (hsa.2 ha.2) (hsb.2 hb.2)
    have hs := PPoly.signB_k_spec ctx B D (PPoly.mulB_k (PPoly.sumB_k (a.sumsPP_k B false [])) (PPoly.sumB_k (b.sumsPP_k B false []))) s
    rw [sumsPP_k_mul]
    refine ⟨?_, PPoly.DegList.cons (hs.2 (PPoly.Deg.mono hd' _ hp.2)) hacc⟩
    rw [PPoly.denoteList_cons, hs.1, hp.1, hsa.1, hsb.1, ha.1, hb.1]
    simp only [PPoly.denoteList, List.foldr_nil, add_zero] <;> rfl
  | pow a k ih =>
    intro D s acc hd hD hacc
    have hd' : a.degB_k * k ≤ D := hd
    have hp := Expr.powPP_k_spec_noB ctx B a k (PPoly.sumB_k (a.sumsPP_k B false [])) (fun hk => by
      have ha := ih a.degB_k false [] (Nat.le_refl _)
        (by have : a.degB_k ≤ a.degB_k * k := Nat.le_mul_of_pos_right _ hk; omega) (fun _ h => by cases h)
      have hsa := PPoly.sumB_k_spec ctx B a.degB_k (a.sumsPP_k B false [])
      refine ⟨?_, hsa.2 ha.2⟩
      rw [hsa.1, ha.1]; exact add_zero _) (by omega)
    have hs := PPoly.signB_k_spec ctx B D (a.powPP_k B k (PPoly.sumB_k (a.sumsPP_k B false []))) s
    rw [sumsPP_k_pow]
    refine ⟨?_, PPoly.DegList.cons (hs.2 (PPoly.Deg.mono hd' _ hp.2)) hacc⟩
    rw [PPoly.denoteList_cons, hs.1, hp.1]

theorem Expr.denote_toPPX_k_noB {α} [CommRing α] (ctx : Nat → α) (B : Nat) (bal : Bool) (e : Expr) (he : e.degB_k < B) :
    (e.toPPX_k B bal).denote ctx B = e.denoteF ctx := by
  cases bal
  · exact denote_toPP_k_noB ctx B e he
  · have h := sumsPP_k_spec_noB ctx B e e.degB_k false [] (Nat.le_refl _) he (fun _ h => by cases h)
    have hs := PPoly.sumB_k_spec ctx B e.degB_k (e.sumsPP_k B false [])
    show (PPoly.sumB_k (e.sumsPP_k B false [])).denote ctx B = _
    rw [hs.1, h.1]; exact add_zero _

theorem Mon.code_k_spec_noB {α} [CommSemiring α] (ctx : Context α) {B : Nat} (m : Mon) (h : m.degree < B) :
    PPoly.dsum B (m.code_k B) = m.degree ∧ PPoly.monDenote (Var.denote ctx) B 0 (m.code_k B) = m.denote ctx := by
  induction m with
  | unit => exact ⟨PPoly.dsum_zero B, PPoly.monDenote_zero (Var.denote ctx) B 0⟩
  | mult pw m ih =>
    have hd : pw.k + m.degree < B := h
    have ih := ih (by omega)
    have hk := PPoly.dsum_mul_pow_noB (B := B) pw.x pw.k (by omega)
    show PPoly.dsum B (Nat.add (Nat.mul pw.k (Nat.pow B pw.x)) (m.code_k B)) = pw.k + m.degree ∧
      PPoly.monDenote (Var.denote ctx) B 0 (Nat.add (Nat.mul pw.k (Nat.pow B pw.x)) (m.code_k B)) = pw.denote ctx * m.denote ctx
    rw [show Nat.mul pw.k (Nat.pow B pw.x) = pw.k * B ^ pw.x from rfl, Nat.add_eq]
    refine ⟨?_, ?_⟩
    · rw [PPoly.dsum_add_noB (B := B) _ _ (by rw [hk, ih.1]; exact hd), hk, ih.1]
    · rw [PPoly.monDenote_add_noB (B := B) (Var.denote ctx) 0 _ _ (by rw [hk, ih.1]; exact hd), PPoly.monDenote_mul_pow_noB (B := B) (Var.denote ctx) 0 pw.x pw.k (by omega),
        ih.2, Nat.zero_add, Power.denote_eq]

theorem Poly.toPP_k_spec_noB {α} [CommRing α] (ctx : Context α) {B : Nat} (p : Poly) (h : p.maxDeg_k < B) :
    (p.toPP_k B).denote (Var.denote ctx) B = p.denote ctx ∧ (p.toPP_k B).Deg B p.maxDeg_k := by
  induction p with
  | num k => exact ⟨rfl, trivial⟩
  | add k m p ih =>
    have hm := Poly.le_maxDeg_k k m p
    have ih := ih (by omega)
    have hc := Mon.code_k_spec_noB ctx (B := B) m (by omega)
    refine ⟨?_, ⟨by rw [hc.1]; exact hm.1, PPoly.Deg.mono hm.2 _ ih.2⟩⟩
    show (k : α) * PPoly.monDenote (Var.denote ctx) B 0 (m.code_k B) + (p.toPP_k B).denote (Var.denote ctx) B = k • m.denote ctx + p.denote ctx
    rw [hc.2, ih.1, zsmul_eq_intCast_mul]

theorem PPoly.mulMonN_k_spec_noB {α} [CommRing α] (ctx : Nat → α) (nrm : Int → Int) (hn : ∀ k, ((nrm k : Int) : α) = (k : α))
    (B D₁ D₂ : Nat) (k : Int) (d v : Nat) (hv : dsum B v ≤ D₁) (hD : D₁ + D₂ < B) (p : PPoly) (hp : p.Deg B D₂) :
    (p.mulMonN_k nrm k d v).denote ctx B = k * monDenote ctx B 0 v * p.denote ctx B ∧ (p.mulMonN_k nrm k d v).Deg B (D₁ + D₂) := by
  induction p with
  | num k' =>
    unfold mulMonN_k
    dsimp only
    have hs : ((nrm (Int.mul_k k k') : Int) : α) = (k : α) * (k' : α) := by rw [hn, Int.mul_k_eq]; exact intCast_mul k k'
    cases hv0 : Nat.beq v 0
    case true =>
      have : v = 0 := Nat.eq_of_beq_eq_true hv0
      subst this
      refine ⟨?_, trivial⟩
      show ((nrm (Int.mul_k k k') : Int) : α) = _ * ((k' : Int) : α)
      rw [hs, monDenote_zero, mul_one]
    dsimp only
    cases h : Int.beqZero_k (nrm (Int.mul_k k k'))
    · refine ⟨?_, ⟨by omega, trivial⟩⟩
      show ((nrm (Int.mul_k k k') : Int) : α) * _ + ((Int.ofNat 0 : Int) : α) = _ * ((k' : Int) : α)
      rw [hs]
      show _ + ((0 : Int) : α) = _
      rw [intCast_zero, add_zero]
      simp only [mul_assoc, mul_comm, mul_left_comm]
    · have h : nrm (Int.mul_k k k') = 0 := by rw [Int.beqZero_k_eq] at h; exact beq_iff_eq.mp h
      refine ⟨?_, trivial⟩
      show ((Int.ofNat 0 : Int) : α) = _ * ((k' : Int) : α)
      rw [show ((Int.ofNat 0 : Int) : α) = 0 from intCast_zero]
      have : (k : α) * (k' : α) = 0 := by rw [← hs, h, intCast_zero]
      calc (0 : α) = (k : α) * (k' : α) * monDenote ctx B 0 v := by rw [this, zero_mul]
        _ = _ := by simp only [mul_assoc, mul_comm, mul_left_comm]
  | add k' d' v' p ih =>
    obtain ⟨ih₁, ih₂⟩ := ih hp.2
    have hs : ((nrm (Int.mul_k k k') : Int) : α) = (k : α) * (k' : α) := by rw [hn, Int.mul_k_eq]; exact intCast_mul k k'
    show (Bool.rec (.add (nrm (Int.mul_k k k')) (Nat.add d d') (Nat.add v v') (p.mulMonN_k nrm k d v)) (p.mulMonN_k nrm k d v)
      (Int.beqZero_k (nrm (Int.mul_k k k'))) : PPoly).denote ctx B = _ ∧
      (Bool.rec (.add (nrm (Int.mul_k k k')) (Nat.add d d') (Nat.add v v') (p.mulMonN_k nrm k d v)) (p.mulMonN_k nrm k d v)
      (Int.beqZero_k (nrm (Int.mul_k k k'))) : PPoly).Deg B (D₁ + D₂)
    cases h : Int.beqZero_k (nrm (Int.mul_k k k'))
    · have hsum := dsum_add_noB (B := B) v v' (by have := hp.1; omega)
      refine ⟨?_, ⟨by rw [Nat.add_eq, hsum]; have := hp.1; omega, ih₂⟩⟩
      show ((nrm (Int.mul_k k k') : Int) : α) * monDenote ctx B 0 (Nat.add v v') + (p.mulMonN_k nrm k d v).denote ctx B =
        _ * ((k' : α) * _ + denote ctx B p)
      rw [ih₁, hs, Nat.add_eq, monDenote_add_noB (B := B) ctx 0 v v' (by have := hp.1; omega), left_distrib]
      simp only [mul_assoc, mul_left_comm]
    · have h : nrm (Int.mul_k k k') = 0 := by rw [Int.beqZero_k_eq] at h; exact beq_iff_eq.mp h
      refine ⟨?_, ih₂⟩
      show (p.mulMonN_k nrm k d v).denote ctx B = _ * ((k' : α) * _ + denote ctx B p)
      have : (k : α) * (k' : α) = 0 := by rw [← hs, h, intCast_zero]
      rw [ih₁, left_distrib]
      have h0 : (k : α) * monDenote ctx B 0 v * ((k' : α) * monDenote ctx B 0 v') = 0 := by
        calc (k : α) * monDenote ctx B 0 v * ((k' : α) * monDenote ctx B 0 v')
            = ((k : α) * (k' : α)) * (monDenote ctx B 0 v * monDenote ctx B 0 v') := by simp only [mul_assoc, mul_left_comm]
          _ = 0 := by rw [this, zero_mul]
      rw [h0, zero_add]

theorem PSumTree.eval_k_spec_noB {α} [CommRing α] (ctx : Context α) (nrm : Int → Int) (hn : ∀ k, ((nrm k : Int) : α) = (k : α))
    {B : Nat} (t : PSumTree) (hok : t.ok_k B = true) (h : t.AllZero ctx B) :
    (t.eval_k nrm B).denote (Var.denote ctx) B = 0 ∧ (t.eval_k nrm B).Deg B (B - 1) := by
  induction t with
  | leaf k m D p =>
    have hok : Nat.blt (Nat.add (Mon.degree_k m) D) B = true := hok
    rw [Nat.blt_eq, Mon.degree_k_eq_degree, Nat.add_eq] at hok
    replace h : p.denote (Var.denote ctx) B = 0 ∧ p.Deg B D := h
    have hc := Mon.code_k_spec_noB ctx (B := B) m (by omega)
    have hm := PPoly.mulMonN_k_spec_noB (Var.denote ctx) nrm hn B m.degree D k (Mon.degree_k m) (m.code_k B) (by rw [hc.1]; exact Nat.le_refl _) hok _ h.2
    refine ⟨?_, PPoly.Deg.mono (by omega) _ hm.2⟩
    show (p.mulMonN_k nrm k (Mon.degree_k m) (m.code_k B)).denote (Var.denote ctx) B = 0
    rw [hm.1, h.1, mul_zero]
  | node a b iha ihb =>
    have hok : Bool.rec false (b.ok_k B) (a.ok_k B) = true := hok
    have hok := PPoly.and_of_rec hok
    obtain ⟨ha, hb⟩ := h
    have ha := iha hok.1 ha
    have hb := ihb hok.2 hb
    have hc := PPoly.combineN_k_spec (Var.denote ctx) nrm hn B (B - 1) (a.eval_k nrm B) (b.eval_k nrm B)
    refine ⟨?_, hc.2 ha.2 hb.2⟩
    show (PPoly.combineN_k nrm (a.eval_k nrm B) (b.eval_k nrm B)).denote (Var.denote ctx) B = 0
    rw [hc.1, ha.1, hb.1, add_zero]

end Lean.Grind.CommRing

open Lean.Grind CommRing


namespace PackedHand

/-- `x₀` packed in base 2 (coefficient 1, degree 1, code 1); squaring it overflows into `x₁`. -/
abbrev X0 : PPoly := .add 1 1 1 (.num 0)
/-- Valuation `xᵢ ↦ i + 2`: `x₀² = 4 ≠ 3 = x₁`. -/
abbrev ctx2 : Nat → Int := fun i => i + 2
theorem X0_deg1 : X0.Deg 2 1 := ⟨by decide +kernel, trivial⟩
/-- Monomial and polynomials `x₀`, `x₁`, `x₀ + 1` as `Mon`/`Poly`. -/
abbrev m0 : Mon := .mult ⟨0, 1⟩ .unit
abbrev P0 : Poly := .add 1 m0 (.num 0)
abbrev P1 : Poly := .add 1 (.mult ⟨1, 1⟩ .unit) (.num 0)
abbrev P0p1 : Poly := .add 1 m0 (.num 1)
/-- Context `x₀ = 0`, `x₁ = 1`. -/
abbrev c01 : Context Int := .branch 1 (.leaf 0) (.leaf 1)
/-- A tree with one zero leaf. -/
abbrev T0 : PSumTree := .leaf 0 .unit 0 (.num 0)
theorem T0_zero (ctx : Context Int) (B : Nat) : T0.AllZero ctx B := by
  unfold PSumTree.AllZero; exact ⟨PPoly.denote_num_zero _ _, trivial⟩

-- `Lean.Grind.CommRing.PPoly.mulMon_k_spec` (hypothesis 11, D₁ + D₂ < B): necessary; D₁ = D₂ = 1, k = 1, v = 1, p = x₀; overflow: base 2, x₀·x₀ packs to code 2 = x₁ (valuation xᵢ ↦ i+2 over Int): 3 ≠ 4
theorem mulMon_k_spec.h11 : ¬ drop0% Lean.Grind.CommRing.PPoly.mulMon_k_spec 11 := fun h => by
  have := (h (α := Int) ctx2 2 1 1 (by decide) 1 1 1 (by decide +kernel) X0 X0_deg1).1
  revert this; decide +kernel
-- `Lean.Grind.CommRing.PPoly.mulMon_k_spec` (hypothesis 13, Lean.Grind.CommRing.PPoly.Deg B D₂ p): necessary; D₁ = 1, D₂ = 0, p = x₀ (degree 1 > D₂); overflow: base 2, x₀·x₀ packs to code 2 = x₁ (valuation xᵢ ↦ i+2 over Int): 3 ≠ 4
theorem mulMon_k_spec.h13 : ¬ drop0% Lean.Grind.CommRing.PPoly.mulMon_k_spec 13 := fun h => by
  have := (h (α := Int) ctx2 2 1 0 (by decide) 1 1 1 (by decide +kernel) (by decide) X0).1
  revert this; decide +kernel
-- `Lean.Grind.CommRing.PPoly.mulTerms_k_spec` (hypothesis 7, D₁ + D₂ < B): necessary; p₁ = p₂ = x₀, D₁ = D₂ = 1; overflow: base 2, x₀·x₀ packs to code 2 = x₁ (valuation xᵢ ↦ i+2 over Int): 3 ≠ 4
theorem mulTerms_k_spec.h7 : ¬ drop0% Lean.Grind.CommRing.PPoly.mulTerms_k_spec 7 := fun h => by
  have := (h (α := Int) ctx2 2 1 1 (by decide) X0 X0 X0_deg1 X0_deg1).1
  revert this; decide +kernel
-- `Lean.Grind.CommRing.PPoly.mulTerms_k_spec` (hypothesis 10, Lean.Grind.CommRing.PPoly.Deg B D₁ p₁): necessary; p₁ = p₂ = x₀, D₁ = 0, D₂ = 1; overflow: base 2, x₀·x₀ packs to code 2 = x₁ (valuation xᵢ ↦ i+2 over Int): 3 ≠ 4
theorem mulTerms_k_spec.h10 : ¬ drop0% Lean.Grind.CommRing.PPoly.mulTerms_k_spec 10 := fun h => by
  have := (h (α := Int) ctx2 2 0 1 (by decide) (by decide) X0 X0 X0_deg1).1
  revert this; decide +kernel
-- `Lean.Grind.CommRing.PPoly.mulTerms_k_spec` (hypothesis 11, Lean.Grind.CommRing.PPoly.Deg B D₂ p₂): necessary; p₁ = p₂ = x₀, D₁ = 1, D₂ = 0; overflow: base 2, x₀·x₀ packs to code 2 = x₁ (valuation xᵢ ↦ i+2 over Int): 3 ≠ 4
theorem mulTerms_k_spec.h11 : ¬ drop0% Lean.Grind.CommRing.PPoly.mulTerms_k_spec 11 := fun h => by
  have := (h (α := Int) ctx2 2 1 0 (by decide) (by decide) X0 X0 X0_deg1).1
  revert this; decide +kernel
-- `Lean.Grind.CommRing.PPoly.mulB_k_spec` (hypothesis 7, D₁ + D₂ < B): necessary; p₁ = p₂ = x₀, D₁ = D₂ = 1; overflow: base 2, x₀·x₀ packs to code 2 = x₁ (valuation xᵢ ↦ i+2 over Int): 3 ≠ 4
theorem mulB_k_spec.h7 : ¬ drop0% Lean.Grind.CommRing.PPoly.mulB_k_spec 7 := fun h => by
  have := (h (α := Int) ctx2 2 1 1 (by decide) X0 X0 X0_deg1 X0_deg1).1
  revert this; decide +kernel
-- `Lean.Grind.CommRing.PPoly.mulB_k_spec` (hypothesis 10, Lean.Grind.CommRing.PPoly.Deg B D₁ p₁): necessary; p₁ = p₂ = x₀, D₁ = 0, D₂ = 1; overflow: base 2, x₀·x₀ packs to code 2 = x₁ (valuation xᵢ ↦ i+2 over Int): 3 ≠ 4
theorem mulB_k_spec.h10 : ¬ drop0% Lean.Grind.CommRing.PPoly.mulB_k_spec 10 := fun h => by
  have := (h (α := Int) ctx2 2 0 1 (by decide) (by decide) X0 X0 X0_deg1).1
  revert this; decide +kernel
-- `Lean.Grind.CommRing.PPoly.mulB_k_spec` (hypothesis 11, Lean.Grind.CommRing.PPoly.Deg B D₂ p₂): necessary; p₁ = p₂ = x₀, D₁ = 1, D₂ = 0; overflow: base 2, x₀·x₀ packs to code 2 = x₁ (valuation xᵢ ↦ i+2 over Int): 3 ≠ 4
theorem mulB_k_spec.h11 : ¬ drop0% Lean.Grind.CommRing.PPoly.mulB_k_spec 11 := fun h => by
  have := (h (α := Int) ctx2 2 1 0 (by decide) (by decide) X0 X0 X0_deg1).1
  revert this; decide +kernel
-- `Lean.Grind.CommRing.PPoly.powB_k_spec` (hypothesis 8, Lean.Grind.CommRing.PPoly.Deg B D p): necessary; p = x₀, D = 0, k = 2; overflow: base 2, x₀·x₀ packs to code 2 = x₁ (valuation xᵢ ↦ i+2 over Int): 3 ≠ 4
theorem powB_k_spec.h8 : ¬ drop0% Lean.Grind.CommRing.PPoly.powB_k_spec 8 := fun h => by
  have := (h (α := Int) ctx2 2 0 (by decide) X0 2 (by decide)).1
  revert this; decide +kernel
-- `Lean.Grind.CommRing.PPoly.powB_k_spec` (hypothesis 9, D * k < B): necessary; p = x₀, D = 1, k = 2; overflow: base 2, x₀·x₀ packs to code 2 = x₁ (valuation xᵢ ↦ i+2 over Int): 3 ≠ 4
theorem powB_k_spec.h9 : ¬ drop0% Lean.Grind.CommRing.PPoly.powB_k_spec 9 := fun h => by
  have := (h (α := Int) ctx2 2 1 (by decide) X0 2 X0_deg1).1
  revert this; decide +kernel
-- `Lean.Grind.CommRing.Expr.powPP_k_spec` (hypothesis 9, a.degB_k * k < B): necessary; a = var 0, k = 2, p = x₀; x₀^2 packs to code 2 = x₁: 3 ≠ 4
theorem powPP_k_spec.h9 : ¬ drop0% Lean.Grind.CommRing.Expr.powPP_k_spec 9 := fun h => by
  have := (h (α := Int) ctx2 2 (by decide) (.var 0) 2 X0 (fun _ => ⟨by decide +kernel, X0_deg1⟩)).1
  revert this; decide +kernel
-- `Lean.Grind.CommRing.PPoly.DegList.cons` (hypothesis 5, Lean.Grind.CommRing.PPoly.DegList B D ps): necessary; B = 2, D = 0, p = num 0, ps = [x₀] with dsum 1 > 0
theorem DegList.cons.h5 : ¬ drop0% Lean.Grind.CommRing.PPoly.DegList.cons 5 := fun h => by
  have h1 : PPoly.dsum 2 1 ≤ 0 := (h (B := 2) (D := 0) (p := .num 0) (ps := [X0]) trivial X0 (by simp)).1
  revert h1; decide +kernel
-- `Lean.Grind.CommRing.Expr.sumsPP_k_spec` (hypothesis 10, D < B): necessary; e = (var 0)^2, D = 2, B = 2: packs to x₁, 3 ≠ 4
theorem sumsPP_k_spec.h10 : ¬ drop0% Lean.Grind.CommRing.Expr.sumsPP_k_spec 10 := fun h => by
  have := (h (α := Int) ctx2 2 (by decide) (.pow (.var 0) 2) 2 false [] (by decide +kernel) (fun _ h => by cases h)).1
  revert this; decide +kernel
-- `Lean.Grind.CommRing.Expr.sumsPP_k_spec` (hypothesis 11, Lean.Grind.CommRing.PPoly.DegList B D acc): necessary; e = num 0, D = 0, acc = [x₀]: the result list contains x₀, degree 1 > 0
theorem sumsPP_k_spec.h11 : ¬ drop0% Lean.Grind.CommRing.Expr.sumsPP_k_spec 11 := fun h => by
  have h1 : PPoly.dsum 2 1 ≤ 0 := ((h (α := Int) ctx2 2 (by decide) (.num 0) 0 false [X0] (by decide +kernel)
    (by decide)).2 X0 (List.mem_cons_of_mem _ (List.mem_singleton.2 rfl))).1
  revert h1; decide +kernel
-- `Lean.Grind.CommRing.Expr.sub_eq_of_toPPX` (hypothesis 10, Lean.Grind.CommRing.Expr.degOk_k B a b = true): necessary; B = 1: var 0 and var 1 both pack to code 1, k = 0, ctx x₀ = 0, x₁ = 1: -1 ≠ 0
theorem sub_eq_of_toPPX.h10 : ¬ drop0% Lean.Grind.CommRing.Expr.sub_eq_of_toPPX 10 := fun h => by
  have := h (α := Int) c01 1 false false (.var 0) (.var 1) ((Expr.var 1).toPPX_k 1 false) 0 rfl rfl
  revert this; decide +kernel
-- `Lean.Grind.CommRing.PPoly.mulMonN_k_spec` (hypothesis 12, Lean.Grind.CommRing.PPoly.dsum B v ≤ D₁): necessary; nrm = id, D₁ = 0, D₂ = 1, v = 1 (dsum 1 > D₁), p = x₀; overflow: base 2, x₀·x₀ packs to code 2 = x₁ (valuation xᵢ ↦ i+2 over Int): 3 ≠ 4
theorem mulMonN_k_spec.h12 : ¬ drop0% Lean.Grind.CommRing.PPoly.mulMonN_k_spec 12 := fun h => by
  have := (h (α := Int) ctx2 id (fun _ => rfl) 2 0 1 (by decide) 1 1 1 (by decide) X0 X0_deg1).1
  revert this; decide +kernel
-- `Lean.Grind.CommRing.PPoly.mulMonN_k_spec` (hypothesis 13, D₁ + D₂ < B): necessary; nrm = id, D₁ = D₂ = 1, v = 1, p = x₀; overflow: base 2, x₀·x₀ packs to code 2 = x₁ (valuation xᵢ ↦ i+2 over Int): 3 ≠ 4
theorem mulMonN_k_spec.h13 : ¬ drop0% Lean.Grind.CommRing.PPoly.mulMonN_k_spec 13 := fun h => by
  have := (h (α := Int) ctx2 id (fun _ => rfl) 2 1 1 (by decide) 1 1 1 (by decide +kernel) X0 X0_deg1).1
  revert this; decide +kernel
-- `Lean.Grind.CommRing.PPoly.mulMonN_k_spec` (hypothesis 15, Lean.Grind.CommRing.PPoly.Deg B D₂ p): necessary; nrm = id, D₁ = 1, D₂ = 0, p = x₀; overflow: base 2, x₀·x₀ packs to code 2 = x₁ (valuation xᵢ ↦ i+2 over Int): 3 ≠ 4
theorem mulMonN_k_spec.h15 : ¬ drop0% Lean.Grind.CommRing.PPoly.mulMonN_k_spec 15 := fun h => by
  have := (h (α := Int) ctx2 id (fun _ => rfl) 2 1 0 (by decide) 1 1 1 (by decide +kernel) (by decide) X0).1
  revert this; decide +kernel

end PackedHand

namespace PackedHand

/-- Leaf `1 · x₀ · (x₀ - 2)`: the product `x₀² - 2x₀` overflows to `x₁ - 2x₀` in base 2. -/
abbrev Tov : PSumTree := .leaf 1 m0 1 (.add 1 1 1 (.num (-2)))
abbrev c23 : Context Int := .branch 1 (.leaf 2) (.leaf 3)

-- `Lean.Grind.CommRing.PSumTree.eval_k_spec` (hypothesis 4, ∀ (k : Int), ↑(nrm k) = ↑k): necessary; nrm = fun _ => 1, tree = one zero leaf: eval gives num 1 ≠ 0
theorem eval_k_spec.h4 : ¬ drop0% Lean.Grind.CommRing.PSumTree.eval_k_spec 4 := fun h => by
  have := (h (α := Int) c01 (fun _ => 1) (B := 2) (by decide) T0 (by decide +kernel) (T0_zero _ _)).1
  revert this; decide +kernel
-- `Lean.Grind.CommRing.PSumTree.eval_k_spec` (hypothesis 8, Lean.Grind.CommRing.PSumTree.ok_k B t = true): necessary; B = 2, leaf 1·x₀·(x₀ - 2) with D = 1 (ok_k false), ctx x₀ = 2, x₁ = 3: product packs to x₁ - 2x₀ = -1 ≠ 0
theorem eval_k_spec.h8 : ¬ drop0% Lean.Grind.CommRing.PSumTree.eval_k_spec 8 := fun h => by
  have := (h (α := Int) c23 id (fun _ => rfl) (B := 2) (by decide) Tov
    (by unfold PSumTree.AllZero; exact ⟨by decide +kernel, ⟨by decide +kernel, trivial⟩⟩)).1
  revert this; decide +kernel
-- `Lean.Grind.CommRing.PSumTree.denote_eq` (hypothesis 4, ∀ (k : Int), ↑(nrm k) = ↑k): necessary; nrm = fun _ => 0 kills the constant: p₁ = num 1, p = num 0, P = num 0, zero tree: 0 ≠ 1
theorem denote_eq.h4 : ¬ drop0% Lean.Grind.CommRing.PSumTree.denote_eq 4 := fun h => by
  have := h (α := Int) c01 (fun _ => 0) 2 (.num 1) (.num 0) (.num 0) T0 (by decide +kernel) rfl rfl (T0_zero _ _)
  revert this; decide +kernel
-- `Lean.Grind.CommRing.PSumTree.denote_eq` (hypothesis 10, Bool.rec false (Bool.rec false (Bool.rec false (Lean.Grind.CommRing...): necessary; B = 1: x₀ and x₁ both pack to code 1; p₁ = x₀, p = x₁, ctx 0, 1
theorem denote_eq.h10 : ¬ drop0% Lean.Grind.CommRing.PSumTree.denote_eq 10 := fun h => by
  have := h (α := Int) c01 id (fun _ => rfl) 1 P0 P1 (P1.toPP_k 1) T0 rfl rfl (T0_zero _ _)
  revert this; decide +kernel
-- `Lean.Grind.CommRing.PSumTree.denote_eq` (hypothesis 11, P = Lean.Grind.CommRing.Poly.toPP_k B p): necessary; p₁ = num 0, p = num 1, P = num 0 (h₂ holds), zero tree
theorem denote_eq.h11 : ¬ drop0% Lean.Grind.CommRing.PSumTree.denote_eq 11 := fun h => by
  have := h (α := Int) c01 id (fun _ => rfl) 2 (.num 0) (.num 1) (.num 0) T0 (by decide +kernel) rfl (T0_zero _ _)
  revert this; decide +kernel
-- `Lean.Grind.CommRing.PSumTree.denote_eq` (hypothesis 12, P = Lean.Grind.CommRing.PPoly.combineN_k nrm (Lean.Grind.CommRing.P...): necessary; p₁ = num 0, p = num 1, P = num 1 (h₁ holds), zero tree
theorem denote_eq.h12 : ¬ drop0% Lean.Grind.CommRing.PSumTree.denote_eq 12 := fun h => by
  have := h (α := Int) c01 id (fun _ => rfl) 2 (.num 0) (.num 1) (.num 1) T0 (by decide +kernel) rfl (T0_zero _ _)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.simpsP` (hypothesis 8, Bool.rec false (Bool.rec false (Bool.rec false (Lean.Grind.CommRing...): necessary; B = 1: x₀ and x₁ both pack to code 1; p₁ = x₀, p = x₁, ctx x₀ = 0, x₁ = 1
theorem simpsP.h8 : ¬ drop0% Lean.Grind.CommRing.Stepwise.simpsP 8 := fun h => by
  have := h (α := Int) c01 1 P0 P1 (P1.toPP_k 1) T0 rfl rfl (T0_zero _ _) (by decide +kernel)
  revert this; decide +kernel
-- `Lean.Grind.CommRing.Stepwise.simpsP` (hypothesis 9, P = Lean.Grind.CommRing.Poly.toPP_k B p): necessary; p₁ = num 0, p = num 1, P = num 0, zero tree
theorem simpsP.h9 : ¬ drop0% Lean.Grind.CommRing.Stepwise.simpsP 9 := fun h => by
  have := h (α := Int) c01 2 (.num 0) (.num 1) (.num 0) T0 (by decide +kernel) rfl (T0_zero _ _) (by decide +kernel)
  revert this; decide +kernel
-- `Lean.Grind.CommRing.Stepwise.simpsP` (hypothesis 10, P = Lean.Grind.CommRing.PPoly.combineN_k (fun k => k) (Lean.Grind.C...): necessary; p₁ = num 0, p = num 1, P = num 1, zero tree
theorem simpsP.h10 : ¬ drop0% Lean.Grind.CommRing.Stepwise.simpsP 10 := fun h => by
  have := h (α := Int) c01 2 (.num 0) (.num 1) (.num 1) T0 (by decide +kernel) rfl (T0_zero _ _) (by decide +kernel)
  revert this; decide +kernel
-- `Lean.Grind.CommRing.Stepwise.simpsP` (hypothesis 12, Lean.Grind.CommRing.Poly.denote ctx p₁ = 0): necessary; p₁ = p = num 1, P = num 1, zero tree: p₁.denote = 0 dropped, 1 ≠ 0
theorem simpsP.h12 : ¬ drop0% Lean.Grind.CommRing.Stepwise.simpsP 12 := fun h => by
  have := h (α := Int) c01 2 (.num 1) (.num 1) (.num 1) T0 (by decide +kernel) rfl rfl (T0_zero _ _)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.simpsPC` (hypothesis 3, Lean.Grind.IsCharP α c): necessary; Int with c = 1 (not IsCharP): nrm = emod 1 erases constants, p₁ = x₀ + 1, p = x₀, ctx x₀ = -1
theorem simpsPC.h3 : ¬ drop0% Lean.Grind.CommRing.Stepwise.simpsPC 3 := fun h => by
  have := h (α := Int) (c := 1) (.leaf (-1)) 2 P0p1 P0 (P0.toPP_k 2) T0 (by decide +kernel) rfl rfl (T0_zero _ _) (by decide +kernel)
  revert this; decide +kernel
-- `Lean.Grind.CommRing.Stepwise.simpsPC` (hypothesis 10, Bool.rec false (Bool.rec false (Bool.rec false (Lean.Grind.CommRing...): necessary; B = 1: x₀ and x₁ both pack to code 1; p₁ = x₀, p = x₁, ctx x₀ = 0, x₁ = 1 (Int, c = 0)
theorem simpsPC.h10 : ¬ drop0% Lean.Grind.CommRing.Stepwise.simpsPC 10 := fun h => by
  have := h (α := Int) (c := 0) c01 1 P0 P1 (P1.toPP_k 1) T0 rfl rfl (T0_zero _ _) (by decide +kernel)
  revert this; decide +kernel
-- `Lean.Grind.CommRing.Stepwise.simpsPC` (hypothesis 11, P = Lean.Grind.CommRing.Poly.toPP_k B p): necessary; p₁ = num 0, p = num 1, P = num 0, zero tree
theorem simpsPC.h11 : ¬ drop0% Lean.Grind.CommRing.Stepwise.simpsPC 11 := fun h => by
  have := h (α := Int) (c := 0) c01 2 (.num 0) (.num 1) (.num 0) T0 (by decide +kernel) rfl (T0_zero _ _) (by decide +kernel)
  revert this; decide +kernel
-- `Lean.Grind.CommRing.Stepwise.simpsPC` (hypothesis 12, P = Lean.Grind.CommRing.PPoly.combineN_k (fun k => k.emod_k (Int.of...): necessary; p₁ = num 0, p = num 1, P = num 1, zero tree
theorem simpsPC.h12 : ¬ drop0% Lean.Grind.CommRing.Stepwise.simpsPC 12 := fun h => by
  have := h (α := Int) (c := 0) c01 2 (.num 0) (.num 1) (.num 1) T0 (by decide +kernel) rfl (T0_zero _ _) (by decide +kernel)
  revert this; decide +kernel
-- `Lean.Grind.CommRing.Stepwise.simpsPC` (hypothesis 14, Lean.Grind.CommRing.Poly.denote ctx p₁ = 0): necessary; p₁ = p = num 1, P = num 1, zero tree: p₁.denote = 0 dropped, 1 ≠ 0
theorem simpsPC.h14 : ¬ drop0% Lean.Grind.CommRing.Stepwise.simpsPC 14 := fun h => by
  have := h (α := Int) (c := 0) c01 2 (.num 1) (.num 1) (.num 1) T0 (by decide +kernel) rfl rfl (T0_zero _ _)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.d_stepsP` (hypothesis 10, Bool.rec false (Bool.rec false (Bool.rec false (Lean.Grind.CommRing...): necessary; k = 0, init = num 0, B = 1: p₁ = x₀, p = x₁ pack equally, ctx x₀ = 0, x₁ = 1
theorem d_stepsP.h10 : ¬ drop0% Lean.Grind.CommRing.Stepwise.d_stepsP 10 := fun h => by
  have := h (α := Int) c01 0 (.num 0) 1 P0 P1 (P1.toPP_k 1) T0 rfl rfl (T0_zero _ _) (by decide +kernel)
  revert this; decide +kernel
-- `Lean.Grind.CommRing.Stepwise.d_stepsP` (hypothesis 11, P = Lean.Grind.CommRing.Poly.toPP_k B p): necessary; k = 0, init = num 0, p₁ = num 0, p = num 1, P = num 0
theorem d_stepsP.h11 : ¬ drop0% Lean.Grind.CommRing.Stepwise.d_stepsP 11 := fun h => by
  have := h (α := Int) c01 0 (.num 0) 2 (.num 0) (.num 1) (.num 0) T0 (by decide +kernel) rfl (T0_zero _ _) (by decide +kernel)
  revert this; decide +kernel
-- `Lean.Grind.CommRing.Stepwise.d_stepsP` (hypothesis 12, P = Lean.Grind.CommRing.PPoly.combineN_k (fun k => k) (Lean.Grind.C...): necessary; k = 0, init = num 0, p₁ = num 0, p = num 1, P = num 1
theorem d_stepsP.h12 : ¬ drop0% Lean.Grind.CommRing.Stepwise.d_stepsP 12 := fun h => by
  have := h (α := Int) c01 0 (.num 0) 2 (.num 0) (.num 1) (.num 1) T0 (by decide +kernel) rfl (T0_zero _ _) (by decide +kernel)
  revert this; decide +kernel
-- `Lean.Grind.CommRing.Stepwise.d_stepsP` (hypothesis 14, ↑k * Lean.Grind.CommRing.Poly.denote ctx init = Lean.Grind.CommRing...): necessary; k = 0, init = num 0, p₁ = p = num 1: 0 ≠ 1
theorem d_stepsP.h14 : ¬ drop0% Lean.Grind.CommRing.Stepwise.d_stepsP 14 := fun h => by
  have := h (α := Int) c01 0 (.num 0) 2 (.num 1) (.num 1) (.num 1) T0 (by decide +kernel) rfl rfl (T0_zero _ _)
  revert this; decide +kernel

-- `Lean.Grind.CommRing.Stepwise.d_stepsPC` (hypothesis 3, Lean.Grind.IsCharP α c): necessary; Int with c = 1 (not IsCharP): nrm = emod 1 erases constants, p₁ = x₀ + 1, p = x₀, k = 0, ctx x₀ = -1
theorem d_stepsPC.h3 : ¬ drop0% Lean.Grind.CommRing.Stepwise.d_stepsPC 3 := fun h => by
  have := h (α := Int) (c := 1) (.leaf (-1)) 0 (.num 0) 2 P0p1 P0 (P0.toPP_k 2) T0 (by decide +kernel) rfl rfl (T0_zero _ _) (by decide +kernel)
  revert this; decide +kernel
-- `Lean.Grind.CommRing.Stepwise.d_stepsPC` (hypothesis 12, Bool.rec false (Bool.rec false (Bool.rec false (Lean.Grind.CommRing...): necessary; k = 0, init = num 0, B = 1: p₁ = x₀, p = x₁ pack equally, ctx x₀ = 0, x₁ = 1 (Int, c = 0)
theorem d_stepsPC.h12 : ¬ drop0% Lean.Grind.CommRing.Stepwise.d_stepsPC 12 := fun h => by
  have := h (α := Int) (c := 0) c01 0 (.num 0) 1 P0 P1 (P1.toPP_k 1) T0 rfl rfl (T0_zero _ _) (by decide +kernel)
  revert this; decide +kernel
-- `Lean.Grind.CommRing.Stepwise.d_stepsPC` (hypothesis 13, P = Lean.Grind.CommRing.Poly.toPP_k B p): necessary; k = 0, init = num 0, p₁ = num 0, p = num 1, P = num 0
theorem d_stepsPC.h13 : ¬ drop0% Lean.Grind.CommRing.Stepwise.d_stepsPC 13 := fun h => by
  have := h (α := Int) (c := 0) c01 0 (.num 0) 2 (.num 0) (.num 1) (.num 0) T0 (by decide +kernel) rfl (T0_zero _ _) (by decide +kernel)
  revert this; decide +kernel
-- `Lean.Grind.CommRing.Stepwise.d_stepsPC` (hypothesis 14, P = Lean.Grind.CommRing.PPoly.combineN_k (fun k => k.emod_k (Int.of...): necessary; k = 0, init = num 0, p₁ = num 0, p = num 1, P = num 1
theorem d_stepsPC.h14 : ¬ drop0% Lean.Grind.CommRing.Stepwise.d_stepsPC 14 := fun h => by
  have := h (α := Int) (c := 0) c01 0 (.num 0) 2 (.num 0) (.num 1) (.num 1) T0 (by decide +kernel) rfl (T0_zero _ _) (by decide +kernel)
  revert this; decide +kernel
-- `Lean.Grind.CommRing.Stepwise.d_stepsPC` (hypothesis 16, ↑k * Lean.Grind.CommRing.Poly.denote ctx init = Lean.Grind.CommRing...): necessary; k = 0, init = num 0, p₁ = p = num 1: 0 ≠ 1
theorem d_stepsPC.h16 : ¬ drop0% Lean.Grind.CommRing.Stepwise.d_stepsPC 16 := fun h => by
  have := h (α := Int) (c := 0) c01 0 (.num 0) 2 (.num 1) (.num 1) (.num 1) T0 (by decide +kernel) rfl rfl (T0_zero _ _)
  revert this; decide +kernel

end PackedHand

namespace PackedHand

abbrev n10 : Context Nat := .branch 1 (.leaf 1) (.leaf 0)
abbrev n01 : Context Nat := .branch 1 (.leaf 0) (.leaf 1)

-- `Lean.Grind.CommRing.le_true_of_toPPX_eqS` (hypothesis 12, Lean.Grind.CommRing.Expr.degSOk_k B a b = true): necessary; Nat, B = 1: var 0 and var 1 pack equally, ctx x₀ = 1, x₁ = 0: 1 ≤ 0 false
theorem le_true_of_toPPX_eqS.h12 : ¬ drop0% Lean.Grind.CommRing.le_true_of_toPPX_eqS 12 := fun h => by
  have := h (α := Nat) n10 1 false false (.var 0) (.var 1) ((Expr.var 1).toPPX_k 1 false) rfl rfl
  revert this; decide +kernel
-- `Lean.Grind.CommRing.lt_false_of_toPPX_eqS` (hypothesis 14, Lean.Grind.CommRing.Expr.degSOk_k B a b = true): necessary; Nat, B = 1: var 0 and var 1 pack equally, ctx x₀ = 0, x₁ = 1: 0 < 1 true
theorem lt_false_of_toPPX_eqS.h14 : ¬ drop0% Lean.Grind.CommRing.lt_false_of_toPPX_eqS 14 := fun h => by
  have := h (α := Nat) n01 1 false false (.var 0) (.var 1) ((Expr.var 1).toPPX_k 1 false) rfl rfl
  revert this; decide +kernel

-- `Lean.Grind.LawfulOfScientific.ofScientific_def` (hypothesis 3, Lean.Grind.LawfulOfScientific α): necessary; Rat with OfScientific returning 0: ofScientific 1 false 0 = 0 ≠ 1
theorem ofScientific_def.h3 : ¬ drop0% Lean.Grind.LawfulOfScientific.ofScientific_def 3 := fun h => by
  have := @h Rat inferInstance ⟨fun _ _ _ => 0⟩ 1 false 0
  revert this; decide +kernel

end PackedHand


namespace PackedHand
open Lean.Grind.Ring.OfSemiring

-- `Lean.Grind.Ring.OfSemiring.r_sym` (hypothesis 4, Lean.Grind.Ring.OfSemiring.r α a b): necessary; Nat, a = (0,0), b = (1,0): r b a needs 1 + k = k
theorem r_sym.h4 : ¬ drop0% Lean.Grind.Ring.OfSemiring.r_sym 4 := fun h => by
  obtain ⟨k, hk⟩ := h (α := Nat) (a := (0, 0)) (b := (1, 0)); omega
-- `Lean.Grind.Ring.OfSemiring.r_trans` (hypothesis 5, Lean.Grind.Ring.OfSemiring.r α a b): necessary; Nat, a = (1,0), b = c = (0,0)
theorem r_trans.h5 : ¬ drop0% Lean.Grind.Ring.OfSemiring.r_trans 5 := fun h => by
  obtain ⟨k, hk⟩ := h (α := Nat) (a := (1, 0)) (b := (0, 0)) (c := (0, 0)) (r_rfl _); omega
-- `Lean.Grind.Ring.OfSemiring.r_trans` (hypothesis 6, Lean.Grind.Ring.OfSemiring.r α b c): necessary; Nat, a = b = (0,0), c = (1,0)
theorem r_trans.h6 : ¬ drop0% Lean.Grind.Ring.OfSemiring.r_trans 6 := fun h => by
  obtain ⟨k, hk⟩ := h (α := Nat) (a := (0, 0)) (b := (0, 0)) (c := (1, 0)) (r_rfl _); omega
-- `Lean.Grind.Ring.OfSemiring.Q.ind` (hypothesis 3, ∀ (a : α × α), β (Lean.Grind.Ring.OfSemiring.Q.mk a)): necessary; β = fun _ => False, q = Q.mk (0,0) over Nat
theorem Q.ind.h3 : ¬ drop0% Lean.Grind.Ring.OfSemiring.Q.ind 3 := fun h =>
  h (α := Nat) (β := fun _ => False) (Q.mk (0, 0))
-- `Lean.Grind.Ring.OfSemiring.Q.exact` (hypothesis 4, Lean.Grind.Ring.OfSemiring.Q.mk a = Lean.Grind.Ring.OfSemiring.Q.mk b): necessary; Nat, a = (1,0), b = (0,0)
theorem Q.exact.h4 : ¬ drop0% Lean.Grind.Ring.OfSemiring.Q.exact 4 := fun h => by
  obtain ⟨k, hk⟩ := h (α := Nat) (a := (1, 0)) (b := (0, 0)); omega

/-- `ℕ ∪ {∞}`: a commutative semiring without additive cancellation (`n + ∞ = ∞`), with `IsCharP _ 0`. -/
inductive NI where
  | fin (n : Nat)
  | inf
deriving DecidableEq

namespace NI
def add : NI → NI → NI
  | fin a, fin b => fin (a + b)
  | _, _ => inf
def mul : NI → NI → NI
  | fin a, fin b => fin (a * b)
  | fin a, inf => if a = 0 then fin 0 else inf
  | inf, fin b => if b = 0 then fin 0 else inf
  | inf, inf => inf
def pow (a : NI) : Nat → NI
  | 0 => fin 1
  | n + 1 => mul (pow a n) a
instance : Add NI := ⟨add⟩
instance : Mul NI := ⟨mul⟩
instance : NatCast NI := ⟨fin⟩
instance : OfNat NI n := ⟨fin n⟩
instance : SMul Nat NI := ⟨fun n a => mul (fin n) a⟩
instance : HPow NI Nat NI := ⟨pow⟩

theorem add_comm' (a b : NI) : add a b = add b a := by
  cases a <;> cases b <;> simp [add, Nat.add_comm]
theorem add_assoc' (a b c : NI) : add (add a b) c = add a (add b c) := by
  cases a <;> cases b <;> cases c <;> simp [add, Nat.add_assoc]
theorem mul_assoc' (a b c : NI) : mul (mul a b) c = mul a (mul b c) := by
  rcases a with ⟨_ | a⟩ | _ <;> rcases b with ⟨_ | b⟩ | _ <;> rcases c with ⟨_ | c⟩ | _ <;> simp only [mul, Nat.succ_ne_zero, Nat.mul_eq_zero, if_false, if_true, Nat.zero_mul, Nat.mul_zero, Nat.mul_assoc, or_self, false_or, or_false]
theorem left_distrib' (a b c : NI) : mul a (add b c) = add (mul a b) (mul a c) := by
  rcases a with ⟨_ | a⟩ | _ <;> rcases b with ⟨_ | b⟩ | _ <;> rcases c with ⟨_ | c⟩ | _ <;> simp only [mul, add, Nat.succ_ne_zero, Nat.mul_eq_zero, Nat.add_eq_zero, if_false, if_true, Nat.zero_mul, Nat.mul_zero, Nat.mul_add, Nat.zero_add, Nat.add_zero, or_self, false_or, or_false, and_false, false_and, Nat.add_succ, Nat.succ_add] <;> (try (congr 1; grind))
theorem right_distrib' (a b c : NI) : mul (add a b) c = add (mul a c) (mul b c) := by
  rcases a with ⟨_ | a⟩ | _ <;> rcases b with ⟨_ | b⟩ | _ <;> rcases c with ⟨_ | c⟩ | _ <;> simp only [mul, add, Nat.succ_ne_zero, Nat.mul_eq_zero, Nat.add_eq_zero, if_false, if_true, Nat.zero_mul, Nat.mul_zero, Nat.add_mul, Nat.zero_add, Nat.add_zero, or_self, false_or, or_false, and_false, false_and, Nat.add_succ, Nat.succ_add] <;> (try (congr 1; grind))

instance : Semiring NI where
  add_zero a := by cases a <;> rfl
  add_comm := add_comm'
  add_assoc := add_assoc'
  mul_assoc := mul_assoc'
  mul_one a := by show mul a (fin 1) = a; cases a <;> simp [mul]
  one_mul a := by show mul (fin 1) a = a; cases a <;> simp [mul]
  left_distrib := left_distrib'
  right_distrib := right_distrib'
  zero_mul a := by show mul (fin 0) a = fin 0; cases a <;> simp [mul]
  mul_zero a := by show mul a (fin 0) = fin 0; cases a <;> simp [mul]
  pow_zero a := rfl
  pow_succ a n := rfl

instance : IsCharP NI 0 where
  ofNat_ext_iff {x y} := by
    simp only [Nat.mod_zero]
    exact ⟨fun h => NI.fin.inj h, fun h => h ▸ rfl⟩
end NI

-- `Lean.Grind.Ring.OfSemiring.toQ_inj` (hypothesis 2, Lean.Grind.AddRightCancel α): necessary; NI = ℕ ∪ {∞} (n + ∞ = ∞, no AddRightCancel): toQ 0 = toQ 1 via k = ∞, but 0 ≠ 1
theorem toQ_inj.h2 : ¬ drop0% Lean.Grind.Ring.OfSemiring.toQ_inj 2 := fun h => by
  have := h (α := NI) (a := .fin 0) (b := .fin 1) (Quot.sound ⟨.inf, rfl⟩)
  cases this
-- `Lean.Grind.Ring.OfSemiring.instIsCharPQOfAddRightCancel` (hypothesis 3, Lean.Grind.AddRightCancel α): necessary; NI = ℕ ∪ {∞} is IsCharP 0 but Q NI is trivial (0 + ∞ = 1 + ∞), so 0 = 1 there
theorem instIsCharPQOfAddRightCancel.h3 : ¬ drop0% Lean.Grind.Ring.OfSemiring.instIsCharPQOfAddRightCancel 3 := fun h => by
  have hc := h (α := NI) (p := 0)
  have := (hc.ofNat_ext_iff (x := 0) (y := 1)).mp (Quot.sound ⟨.inf, rfl⟩)
  simp at this
-- `Lean.Grind.Ring.OfSemiring.instIsCharPQOfAddRightCancel` (hypothesis 4, Lean.Grind.IsCharP α p): necessary; Nat with p = 1: then 0 = 1 in Q Nat, refuted by Q.exact
theorem instIsCharPQOfAddRightCancel.h4 : ¬ drop0% Lean.Grind.Ring.OfSemiring.instIsCharPQOfAddRightCancel 4 := fun h => by
  have hc := h (α := Nat) (p := 1)
  have := (hc.ofNat_ext_iff (x := 0) (y := 1)).mpr rfl
  obtain ⟨k, hk⟩ := Q.exact this; omega

end PackedHand

namespace PackedHand
open Lean.Grind.Ring.OfSemiring

/-- `Nat` with its semiring and order, but `<` is always false (not `LawfulOrderLT`). -/
def NL := Nat
instance : Semiring NL := inferInstanceAs (Semiring Nat)
instance : LE NL := inferInstanceAs (LE Nat)
instance : LT NL := ⟨fun _ _ => False⟩
instance : Std.IsPreorder NL := inferInstanceAs (Std.IsPreorder Nat)
instance : OrderedAdd NL := inferInstanceAs (OrderedAdd Nat)

-- `Lean.Grind.Ring.OfSemiring.toQ_lt` (hypothesis 4, Std.LawfulOrderLT α): necessary; NL = Nat with < always false: toQ 0 < toQ 1 holds in Q (defined from ≤) but 0 < 1 fails
theorem toQ_lt.h4 : ¬ drop0% Lean.Grind.Ring.OfSemiring.toQ_lt 4 := fun h => by
  have := (h (α := NL) (a := (0 : Nat)) (b := (1 : Nat))).mp
    (show (0 : Nat) + 0 ≤ 0 + 1 ∧ ¬ ((1 : Nat) + 0 ≤ 0 + 0) by decide)
  exact this

/-- `Nat` with `≤` always true and the usual `<`: an `OrderedRing` with `ExistsAddOfLT`, not `LawfulOrderLT`. -/
def NT := Nat
instance : Semiring NT := inferInstanceAs (Semiring Nat)
instance : LE NT := ⟨fun _ _ => True⟩
instance : LT NT := inferInstanceAs (LT Nat)
instance : Std.IsPreorder NT where
  le_refl _ := trivial
  le_trans _ _ _ _ _ := trivial
instance : OrderedRing NT where
  add_le_left_iff _ := ⟨fun _ => trivial, fun _ => trivial⟩
  zero_lt_one := Nat.zero_lt_one
  mul_lt_mul_of_pos_left {a b c} h hc := Nat.mul_lt_mul_of_pos_left (k := c) h hc
  mul_lt_mul_of_pos_right {a b c} h hc := Nat.mul_lt_mul_of_pos_right (k := c) h hc
instance : ExistsAddOfLT NT where
  exists_add_of_le {a b} h := ⟨Nat.sub b a, Nat.sub_pos_of_lt h, (Nat.add_sub_cancel' (Nat.le_of_lt h)).symm⟩

-- `Lean.Grind.Ring.OfSemiring.instOrderedRingQOfLawfulOrderLTOfExistsAddOfLT` (hypothesis 4, Std.LawfulOrderLT α): necessary; NT = Nat with ≤ always true and the usual <: an OrderedRing with ExistsAddOfLT, but in Q NT 0 < 1 needs ¬ 1 ≤ 0
theorem instOrderedRingQOfLawfulOrderLTOfExistsAddOfLT.h4 : ¬ drop0% Lean.Grind.Ring.OfSemiring.instOrderedRingQOfLawfulOrderLTOfExistsAddOfLT 4 := fun h => by
  have := (h (α := NT)).zero_lt_one
  exact this.2 trivial

-- `Lean.Grind.CommRing.Expr.denote_mapCtx_toQ` (hypothesis 4, e.semi_k = true): necessary; Nat, e = intCast 1: ring denotation 1, semiring-as-ring denotation 0, and 1 ≠ 0 in Q Nat (Q.exact)
theorem denote_mapCtx_toQ.h4 : ¬ drop0% Lean.Grind.CommRing.Expr.denote_mapCtx_toQ 4 := fun h => by
  have := h (α := Nat) (.leaf 0) (.intCast 1)
  obtain ⟨k, hk⟩ := Q.exact (a := (1, 0)) (b := (0, 0)) this
  omega

end PackedHand

namespace PackedHand
open Lean.Grind Lean.Grind.Ring.OfSemiring
/-- `Fin 2` (characteristic 2, so `2 • 1 = 2 • 0`) is additively cancellative. -/
instance fin2RightCancel : AddRightCancel (Fin 2) := ⟨by decide⟩

-- `Lean.Grind.Ring.OfSemiring.instNoNatZeroDivisorsQOfAddRightCancel` (hypothesis 3, Lean.Grind.NoNatZeroDivisors α): necessary; Fin 2 (cancellative, characteristic 2): 2 • toQ 1 = 2 • toQ 0 in Q (Fin 2) but toQ 1 ≠ toQ 0 (Q.exact)
theorem instNoNatZeroDivisorsQOfAddRightCancel.h3 : ¬ drop0% Lean.Grind.Ring.OfSemiring.instNoNatZeroDivisorsQOfAddRightCancel 3 := fun h => by
  have hc := h (α := Fin 2)
  have := hc.no_nat_zero_divisors 2 (toQ 1) (toQ 0) (by decide) rfl
  obtain ⟨k, hk⟩ := Q.exact this
  revert k hk; decide
end PackedHand

namespace PackedHand
open Lean.Grind Lean.Grind.Ring.OfSemiring

/-- In any semiring, `k • x + c = k • y + c` gives `k • (x + c) = k • (y + c)`, since `k • c = c + (k - 1) • c`. -/
theorem nsmul_add_cancel_shift {α : Type u} [Semiring α] (k : Nat) (hk : k ≠ 0) (x y c : α)
    (h : k • x + c = k • y + c) : k • (x + c) = k • (y + c) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have e : ∀ z : α, (j + 1) • (z + c) = ((j + 1) • z + c) + j • c := by
    intro z
    rw [Semiring.nsmul_eq_natCast_mul, Semiring.nsmul_eq_natCast_mul, Semiring.nsmul_eq_natCast_mul,
      Semiring.left_distrib, show ((j + 1 : Nat) : α) * c = (j : α) * c + c by
        rw [Semiring.natCast_add, Semiring.right_distrib, Semiring.natCast_one, Semiring.one_mul],
      Semiring.add_comm ((j : α) * c) c, ← Semiring.add_assoc]
  rw [e, e, h]

theorem noNatZeroDivisors_Q {α : Type u} [Semiring α] [NoNatZeroDivisors α] :
    NoNatZeroDivisors (Q α) := ⟨by
  intro k a b hk h
  induction a using Quot.ind with | _ a
  induction b using Quot.ind with | _ b
  obtain ⟨a₁, a₂⟩ := a; obtain ⟨b₁, b₂⟩ := b
  obtain ⟨c, hc⟩ := Q.exact (a := ((k : α) * a₁ + 0 * a₂, (k : α) * a₂ + 0 * a₁))
    (b := ((k : α) * b₁ + 0 * b₂, (k : α) * b₂ + 0 * b₁)) h
  simp only [Semiring.zero_mul, Semiring.add_zero, ← Semiring.nsmul_eq_natCast_mul] at hc
  have hc' : k • (a₁ + b₂) + c = k • (a₂ + b₁) + c := by
    rw [Semiring.nsmul_eq_natCast_mul, Semiring.nsmul_eq_natCast_mul, Semiring.left_distrib,
      Semiring.left_distrib, ← Semiring.nsmul_eq_natCast_mul, ← Semiring.nsmul_eq_natCast_mul,
      ← Semiring.nsmul_eq_natCast_mul, ← Semiring.nsmul_eq_natCast_mul]
    exact hc
  have := NoNatZeroDivisors.no_nat_zero_divisors k _ _ hk (nsmul_add_cancel_shift k hk _ _ c hc')
  exact Quot.sound ⟨c, this⟩⟩

-- `Lean.Grind.Ring.OfSemiring.instNoNatZeroDivisorsQOfAddRightCancel` (hypothesis 2, Lean.Grind.AddRightCancel α): removable; k•x + c = k•y + c gives k•(x + c) = k•(y + c) because k•c = c + (k-1)•c, so NoNatZeroDivisors α alone yields x + c = y + c, i.e. equality in Q (noNatZeroDivisors_Q)
theorem instNoNatZeroDivisorsQOfAddRightCancel.h2 : drop% Lean.Grind.Ring.OfSemiring.instNoNatZeroDivisorsQOfAddRightCancel 2 := @noNatZeroDivisors_Q
end PackedHand


namespace PackedHand

-- `Lean.Grind.CommRing.PPoly.dsum_div_le` (hypothesis 1, 1 < B): removable; for B ≤ 1 dsum is constantly 0
theorem PPoly.dsum_div_le.h1 : drop% Lean.Grind.CommRing.PPoly.dsum_div_le 1 := @Lean.Grind.CommRing.PPoly.dsum_div_le_noB

-- `Lean.Grind.CommRing.PPoly.dsum_add` (hypothesis 1, 1 < B): removable; for B ≤ 1 dsum is constantly 0
theorem PPoly.dsum_add.h1 : drop% Lean.Grind.CommRing.PPoly.dsum_add 1 := @Lean.Grind.CommRing.PPoly.dsum_add_noB

-- `Lean.Grind.CommRing.PPoly.monDenote_add` (hypothesis 4, 1 < B): removable; for B ≤ 1 monDenote is constantly 1
theorem PPoly.monDenote_add.h4 : drop% Lean.Grind.CommRing.PPoly.monDenote_add 4 := @Lean.Grind.CommRing.PPoly.monDenote_add_noB

-- `Lean.Grind.CommRing.PPoly.dsum_mul_pow` (hypothesis 1, 1 < B): removable; k < B ≤ 1 forces k = 0, and dsum B 0 = 0
theorem PPoly.dsum_mul_pow.h1 : drop% Lean.Grind.CommRing.PPoly.dsum_mul_pow 1 := @Lean.Grind.CommRing.PPoly.dsum_mul_pow_noB

-- `Lean.Grind.CommRing.PPoly.monDenote_mul_pow` (hypothesis 4, 1 < B): removable; k < B ≤ 1 forces k = 0, and monDenote is 1 = x^0
theorem PPoly.monDenote_mul_pow.h4 : drop% Lean.Grind.CommRing.PPoly.monDenote_mul_pow 4 := @Lean.Grind.CommRing.PPoly.monDenote_mul_pow_noB

-- `Lean.Grind.CommRing.PPoly.mulMon_k_spec` (hypothesis 6, 1 < B): removable; the library proof uses 1 < B only through dsum_add/monDenote_add, which hold without it
theorem PPoly.mulMon_k_spec.h6 : drop% Lean.Grind.CommRing.PPoly.mulMon_k_spec 6 := @Lean.Grind.CommRing.PPoly.mulMon_k_spec_noB

-- `Lean.Grind.CommRing.PPoly.mulTerms_k_spec` (hypothesis 6, 1 < B): removable; library proof with mulMon_k_spec without 1 < B
theorem PPoly.mulTerms_k_spec.h6 : drop% Lean.Grind.CommRing.PPoly.mulTerms_k_spec 6 := @Lean.Grind.CommRing.PPoly.mulTerms_k_spec_noB

-- `Lean.Grind.CommRing.PPoly.mulB_k_spec` (hypothesis 6, 1 < B): removable; library proof with mulMon_k_spec/mulTerms_k_spec without 1 < B
theorem PPoly.mulB_k_spec.h6 : drop% Lean.Grind.CommRing.PPoly.mulB_k_spec 6 := @Lean.Grind.CommRing.PPoly.mulB_k_spec_noB

-- `Lean.Grind.CommRing.PPoly.powB_k_spec` (hypothesis 5, 1 < B): removable; library proof with mulB_k_spec without 1 < B
theorem PPoly.powB_k_spec.h5 : drop% Lean.Grind.CommRing.PPoly.powB_k_spec 5 := @Lean.Grind.CommRing.PPoly.powB_k_spec_noB

-- `Lean.Grind.CommRing.Expr.powPP_k_spec` (hypothesis 4, 1 < B): removable; library proof with powB_k_spec, dsum_mul_pow, monDenote_mul_pow without 1 < B (k < B suffices)
theorem Expr.powPP_k_spec.h4 : drop% Lean.Grind.CommRing.Expr.powPP_k_spec 4 := @Lean.Grind.CommRing.Expr.powPP_k_spec_noB

-- `Lean.Grind.CommRing.Expr.toPPAcc_k_spec` (hypothesis 4, 1 < B): removable; library proof with the B-free lemmas; in the variable case 1 = degree ≤ D < B gives 1 < B
theorem Expr.toPPAcc_k_spec.h4 : drop% Lean.Grind.CommRing.Expr.toPPAcc_k_spec 4 := @Lean.Grind.CommRing.Expr.toPPAcc_k_spec_noB

-- `Lean.Grind.CommRing.Expr.denote_toPP_k` (hypothesis 4, 1 < B): removable; library proof with toPPAcc_k_spec without 1 < B
theorem Expr.denote_toPP_k.h4 : drop% Lean.Grind.CommRing.Expr.denote_toPP_k 4 := @Lean.Grind.CommRing.Expr.denote_toPP_k_noB

-- `Lean.Grind.CommRing.Expr.sumsPP_k_spec` (hypothesis 4, 1 < B): removable; library proof with the B-free lemmas; in the variable case 1 = degree ≤ D < B gives 1 < B
theorem Expr.sumsPP_k_spec.h4 : drop% Lean.Grind.CommRing.Expr.sumsPP_k_spec 4 := @Lean.Grind.CommRing.Expr.sumsPP_k_spec_noB

-- `Lean.Grind.CommRing.Expr.denote_toPPX_k` (hypothesis 4, 1 < B): removable; library proof with denote_toPP_k/sumsPP_k_spec without 1 < B
theorem Expr.denote_toPPX_k.h4 : drop% Lean.Grind.CommRing.Expr.denote_toPPX_k 4 := @Lean.Grind.CommRing.Expr.denote_toPPX_k_noB

-- `Lean.Grind.CommRing.Mon.code_k_spec` (hypothesis 4, 1 < B): removable; library proof with dsum_add, monDenote_add, dsum_mul_pow, monDenote_mul_pow without 1 < B (each power k < B)
theorem Mon.code_k_spec.h4 : drop% Lean.Grind.CommRing.Mon.code_k_spec 4 := @Lean.Grind.CommRing.Mon.code_k_spec_noB

-- `Lean.Grind.CommRing.Poly.toPP_k_spec` (hypothesis 4, 1 < B): removable; library proof with Mon.code_k_spec without 1 < B
theorem Poly.toPP_k_spec.h4 : drop% Lean.Grind.CommRing.Poly.toPP_k_spec 4 := @Lean.Grind.CommRing.Poly.toPP_k_spec_noB

-- `Lean.Grind.CommRing.PPoly.mulMonN_k_spec` (hypothesis 8, 1 < B): removable; library proof with dsum_add/monDenote_add without 1 < B
theorem PPoly.mulMonN_k_spec.h8 : drop% Lean.Grind.CommRing.PPoly.mulMonN_k_spec 8 := @Lean.Grind.CommRing.PPoly.mulMonN_k_spec_noB

-- `Lean.Grind.CommRing.PSumTree.eval_k_spec` (hypothesis 6, 1 < B): removable; library proof with Mon.code_k_spec/mulMonN_k_spec without 1 < B; ok_k bounds the degrees
theorem PSumTree.eval_k_spec.h6 : drop% Lean.Grind.CommRing.PSumTree.eval_k_spec 6 := @Lean.Grind.CommRing.PSumTree.eval_k_spec_noB

end PackedHand
