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


namespace W2c0
open Cslib.Circuits

-- the interpretation of the empty signature (from Probe1)
def emptyI : Cslib.Circuits.Interpretation ⟨Empty, Empty.elim⟩ Bool := fun op => op.elim
theorem emptySigNotComplete : ¬ Cslib.Circuits.Interpretation.IsComplete emptyI := by
  intro hc
  obtain ⟨c, -⟩ := hc.exists_computes_single (n := 0) (fun _ => true)
  rcases c with ⟨_ | ⟨p, ⟨op, _⟩⟩, out⟩
  · cases out 0 with
    | input i => exact i.elim0
    | gate g => exact g.elim0
  · exact op.elim

-- no zero-gate circuit computes negation on one input (from Probe1)
theorem noZeroNot {σ : Cslib.Circuits.Signature} (I : Cslib.Circuits.Interpretation σ Bool)
    (c : Cslib.Circuits.Circuit σ 1 1) (hs : c.size = 0)
    (hc : c.ComputesOn I Set.univ (fun x _ => !x 0)) : False := by
  rcases c with ⟨_ | ⟨p, l⟩, out⟩
  · have := congrFun (hc (Set.mem_univ (fun _ => true))) 0
    cases h : out 0 with
    | input i => simp [Cslib.Circuits.Circuit.eval, h] at this
    | gate g => exact g.elim0
  · simp at hs

-- every circuit over the empty signature has no gates
theorem eSize0 {n m : ℕ} (c : Circuit ⟨Empty, Empty.elim⟩ n m) : c.size = 0 := by
  rcases c with ⟨_ | ⟨p, ⟨op, _⟩⟩, out⟩
  · rfl
  · exact op.elim

def notF : (Fin 1 → Bool) → Fin 1 → Bool := fun x _ => !x 0

theorem eNoNot (c : Circuit ⟨Empty, Empty.elim⟩ 1 1) : ¬ c.ComputesOn emptyI Set.univ notF :=
  fun hc => noZeroNot _ c (eSize0 c) hc

theorem eTop : ecomplexityOn emptyI Set.univ notF = ⊤ := by
  by_contra h
  obtain ⟨c, hc⟩ := ecomplexityOn_ne_top_iff.mp h
  exact eNoNot c hc

abbrev BI := Boolean.interpretation

theorem bNot : 1 ≤ complexityOn BI Set.univ notF :=
  le_complexityOn_iff.mpr fun c hc => by
    by_contra hlt
    exact noZeroNot _ c (by omega) hc

-- the one-gate NOT circuit
def notC : Circuit Boolean.signature 1 1 := ⟨.gate .empty ⟨.not, fun _ => .input 0⟩, fun _ => .gate 0⟩

theorem notC_computes : notC.Computes BI notF := fun x => by
  funext j; rfl

theorem emptyNotSim : ¬ emptyI.Simulates BI := fun ⟨_, h⟩ => by
  obtain ⟨c, hc, -⟩ := h .not
  exact eNoNot c (hc.computesOn Set.univ)

end W2c0
open W2c0 Cslib.Circuits


namespace W2c0
-- one nullary operation, and one unary operation
abbrev uS : Signature := ⟨Unit, fun _ => 0⟩
abbrev u1S : Signature := ⟨Unit, fun _ => 1⟩
-- the one-gate program over `uS`
def p1 : Program uS 0 1 := .gate .empty ⟨(), Fin.elim0⟩
end W2c0


namespace W2c0
universe u v
-- infinitely many nullary operations
abbrev nS : Signature := ⟨ℕ, fun _ => 0⟩
instance lineInf {n g : ℕ} : Infinite (Line nS n g) :=
  Infinite.of_injective (fun k : ℕ => (⟨k, Fin.elim0⟩ : Line nS n g)) (fun _ _ h => congrArg Line.op h)
-- one binary operation `x ∧ ¬ y`
abbrev aS : Signature := ⟨Unit, fun _ => 2⟩
def aI : Interpretation aS Bool := fun _ x => x 0 && !x 1
theorem proj_mem (i : Fin 3) : (fun x => x i) ∈ computableFunctions aI 3 1 :=
  mem_computableFunctions.mpr ⟨Circuit.wiring _ (fun _ => i), fun _ => funext fun _ => rfl, by simp⟩
theorem gc_mem (i j : Fin 3) : (fun x => x i && !x j) ∈ computableFunctions aI 3 1 :=
  mem_computableFunctions.mpr ⟨⟨.gate .empty ⟨(), ![.input i, .input j]⟩, fun _ => .gate 0⟩,
    fun _ => funext fun _ => rfl, le_rfl⟩
theorem nine : 9 ≤ (computableFunctions aI 3 1).card := by
  have hs : ({fun x => x 0, fun x => x 1, fun x => x 2, fun x => x 0 && !x 1, fun x => x 0 && !x 2,
      fun x => x 1 && !x 0, fun x => x 1 && !x 2, fun x => x 2 && !x 0, fun x => x 2 && !x 1} :
      Finset ((Fin 3 → Bool) → Bool)) ⊆ computableFunctions aI 3 1 := by
    intro f hf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact proj_mem _ | exact gc_mem _ _
  exact le_trans (by decide) (Finset.card_le_card hs)
-- a size-0 single-output circuit outputs an input
theorem size0proj {σ : Signature.{v}} {U : Type u} {n : ℕ} (I : Interpretation σ U) (c : Circuit σ n 1)
    (hs : c.size = 0) : ∃ i, ∀ x, c.eval I x 0 = x i := by
  rcases c with ⟨_ | ⟨p, l⟩, out⟩
  · cases h : out 0 with
    | input i => exact ⟨i, fun x => by simp [Circuit.eval, h]⟩
    | gate g => exact g.elim0
  · simp at hs
def eIU : Interpretation ⟨Empty, Empty.elim⟩ Unit := fun op => op.elim
end W2c0


namespace W2c0
universe u v
-- Line.card without finiteness of the operations
theorem lineCard {σ : Signature.{v}} (n g : ℕ) :
    Nat.card (Line σ n g) = ∑ᶠ op : σ.Op, (n + g) ^ σ.Arity op := by
  by_cases hf : Finite σ.Op
  · exact Line.card n g
  rw [Nat.card_congr (Line.equiv σ n g)]
  have mem : ∀ op (w : Fin (σ.Arity op) → Wire n g),
      op ∈ Function.support fun op : σ.Op => (n + g) ^ σ.Arity op := by
    intro op w
    rw [Function.mem_support]
    rcases Nat.eq_zero_or_pos (σ.Arity op) with h0 | hpos
    · simp [h0]
    · apply pow_ne_zero
      cases w ⟨0, hpos⟩ with
      | input i => have := i.pos; omega
      | gate j => have := j.pos; omega
  by_cases hs : (Function.support fun op : σ.Op => (n + g) ^ σ.Arity op).Finite
  · let e : (Σ op : σ.Op, Fin (σ.Arity op) → Wire n g) ≃
        Σ op : hs.toFinset, (Fin (σ.Arity op.1) → Wire n g) :=
      { toFun := fun x => ⟨⟨x.1, by rw [Set.Finite.mem_toFinset]; exact mem x.1 x.2⟩, x.2⟩
        invFun := fun x => ⟨x.1.1, x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e, Nat.card_sigma, finsum_eq_sum _ hs]
    simp [Nat.card_eq_fintype_card]
    exact Finset.sum_coe_sort hs.toFinset (fun op => (n + g) ^ σ.Arity op)
  · rw [finsum_of_infinite_support hs]
    have hne : ∀ op ∈ Function.support fun op : σ.Op => (n + g) ^ σ.Arity op,
        Nonempty (Fin (σ.Arity op) → Wire n g) := by
      intro op hop
      by_cases hw : n + g = 0
      · have : σ.Arity op = 0 := by
          by_contra h0
          exact hop (by simp [hw, h0])
        exact ⟨fun i => absurd i.isLt (by omega)⟩
      · exact ⟨fun _ => if h : 0 < n then .input ⟨0, h⟩ else .gate ⟨0, by omega⟩⟩
    have hinf : Infinite (Function.support fun op : σ.Op => (n + g) ^ σ.Arity op) := Set.Infinite.to_subtype (s := Function.support fun op : σ.Op => (n + g) ^ σ.Arity op) hs
    have : Infinite (Σ op : σ.Op, Fin (σ.Arity op) → Wire n g) :=
      Infinite.of_injective (fun op : Function.support (fun op : σ.Op => (n + g) ^ σ.Arity op) =>
        (⟨op.1, Classical.choice (hne op.1 op.2)⟩ : Σ op : σ.Op, Fin (σ.Arity op) → Wire n g))
        (fun a b h => Subtype.ext (congrArg Sigma.fst h))
    exact Nat.card_eq_zero_of_infinite

theorem progCard {σ : Signature.{v}} (n g : ℕ) :
    Nat.card (Program σ n g) = ∏ j ∈ Finset.range g, ∑ᶠ op : σ.Op, (n + j) ^ σ.Arity op := by
  induction g with
  | zero => simp
  | succ g ih => rw [Program.card_succ, ih, lineCard, Finset.prod_range_succ]

def ar1 : ℕ → ℕ
  | 0 => 0
  | _ + 1 => 1

-- an injective encoding of the first `m` inputs
def enc {U : Type u} {n : ℕ} (e : U × U → U) (u0 : U) : ℕ → (Fin n → U) → U
  | 0 => fun _ => u0
  | m + 1 => fun x => if h : m < n then e (enc e u0 m x, x ⟨m, h⟩) else enc e u0 m x

theorem enc_synth {U : Type u} {n : ℕ} (e : U × U → U) (u0 : U) (m : ℕ) :
    ∃ cost, Synthesis (fullInterpretation (k := 2)) (inputs n) {enc e u0 m} cost := by
  induction m with
  | zero => exact ⟨1, Synthesis.full_const u0⟩
  | succ m ih =>
    obtain ⟨c, hc⟩ := ih
    by_cases h : m < n
    · have : enc (n := n) e u0 (m + 1) = fun x => (fun a b => e (a, b)) (enc e u0 m x) (x ⟨m, h⟩) :=
        funext fun x => by simp [enc, h]
      rw [this]
      exact ⟨_, hc.full_binary (Synthesis.of_mem (f := fun x => x ⟨m, h⟩) ⟨⟨m, h⟩, rfl⟩)
        (fun a b => e (a, b))⟩
    · have : enc (n := n) e u0 (m + 1) = enc e u0 m := funext fun x => by simp [enc, h]
      rw [this]; exact ⟨c, hc⟩

theorem enc_inj {U : Type u} {n : ℕ} (e : U × U → U) (he : Function.Injective e) (u0 : U) (m : ℕ) :
    ∀ x y : Fin n → U, enc e u0 m x = enc e u0 m y → ∀ i : Fin n, i.val < m → x i = y i := by
  induction m with
  | zero => intro x y _ i hi; omega
  | succ m ih =>
    intro x y hxy i hi
    by_cases h : m < n
    · simp only [enc, h, dite_true] at hxy
      obtain ⟨h1, h2⟩ := Prod.mk.inj (he hxy)
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
      · exact ih x y h1 i hi
      · have : i = ⟨m, h⟩ := Fin.ext hi
        subst this; exact h2
    · simp only [enc, h, dite_false] at hxy
      exact ih x y hxy i (by have := i.isLt; omega)

-- the binary full basis is complete on every carrier (pairing on infinite carriers)
theorem complete2 (U : Type u) : (fullInterpretation (k := 2) (Carrier := U)).IsComplete := by
  by_cases hf : Finite U
  · exact fullInterpretation_isComplete le_rfl
  have : Infinite U := not_finite_iff_infinite.mp hf
  obtain ⟨e⟩ : Nonempty (U × U ≃ U) := Cardinal.eq.mp (by
    simp only [Cardinal.mk_prod, Cardinal.lift_id]
    exact Cardinal.mul_eq_self (Cardinal.aleph0_le_mk U))
  obtain ⟨u0⟩ : Nonempty U := inferInstance
  constructor
  intro n f
  obtain ⟨c, hc⟩ := enc_synth (n := n) e u0 n
  have hinj : Function.Injective (enc e u0 n : (Fin n → U) → U) := fun x y h =>
    funext fun i => enc_inj e e.injective u0 n x y h i i.isLt
  have hs := Synthesis.full_gate_of_syntheses (k := 2) (r := 1) (by norm_num)
    (fun v => f (Function.invFun (enc e u0 n) (v 0))) (fun _ => enc e u0 n) (fun _ => c) (fun _ => hc)
  have hf : (fun x => (fun v => f (Function.invFun (enc e u0 n) (v 0))) (fun i => (fun _ => enc e u0 n) i x))
      = f := funext fun x => by simp [Function.leftInverse_invFun hinj x]
  rw [hf] at hs
  obtain ⟨d, hd, -⟩ := hs.exists_circuit
  exact ⟨d, hd⟩

-- over the arity-0 full basis every gate is constant
theorem constGates {n g : ℕ} (p : Program (fullSignature 0 Bool) n g) (x y : Fin n → Bool) :
    p.eval fullInterpretation x = p.eval fullInterpretation y := by
  induction p with
  | empty => funext j; exact j.elim0
  | gate q line ih =>
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [Program.eval_gate_last]
      rcases line with ⟨op, w⟩
      cases op with
      | fn f => exact congrArg f (funext fun i => Fin.elim0 i)
      | con c => rfl
    · simp [ih]

theorem notFull0 (c : Circuit (fullSignature 0 Bool) 1 1) : ¬ c.Computes fullInterpretation notF := by
  intro hc
  rcases c with ⟨p, out⟩
  have h1 := congrFun (hc (fun _ => true)) 0
  have h2 := congrFun (hc (fun _ => false)) 0
  simp only [Circuit.eval, Program.trace, Function.comp_apply, notF] at h1 h2
  cases hw : out 0 with
  | input i => rw [hw] at h1; simp at h1
  | gate j =>
    rw [hw] at h1 h2
    simp only [Wire.elim_gate] at h1 h2
    rw [constGates p (fun _ => true) (fun _ => false)] at h1
    simp_all
end W2c0


namespace W2c0
-- with at most one gate of the full basis, a function is an input, a constant, or one gate on inputs
theorem oneGate {k n c : ℕ} (T : (Fin n → Bool) → Bool)
    (h : Synthesis (fullInterpretation (k := k)) (inputs n) {T} c) (hc : c ≤ 1) :
    (∃ i, ∀ x, T x = x i) ∨ (∃ b, ∀ x : Fin n → Bool, T x = b) ∨
      (∃ (F : (Fin k → Bool) → Bool) (w : Fin k → Fin n), ∀ x, T x = F (x ∘ w)) := by
  obtain ⟨g, p, hg, -, hT⟩ := h 0 .empty (inputs_subset_available _)
  obtain ⟨w, hw⟩ := mem_available.mp (hT rfl)
  rcases w with i | j
  · exact Or.inl ⟨i, fun x => (hw x).symm⟩
  · have hg1 : g = 1 := by have := j.pos; omega
    subst hg1
    rcases p with _ | ⟨q, ⟨op, ws⟩⟩
    cases q
    have hj : j = Fin.last 0 := Subsingleton.elim _ _
    subst hj
    simp only [Program.trace, Wire.elim_gate, Program.eval_gate_last, Line.eval] at hw
    cases op with
    | con b => exact Or.inr (Or.inl ⟨b, fun x => (hw x).symm⟩)
    | fn F =>
      have hex : ∀ a, ∃ i, ws a = .input i := fun a => by
        cases h : ws a with
        | input i => exact ⟨i, rfl⟩
        | gate j => exact j.elim0
      choose w' hw' using hex
      refine Or.inr (Or.inr ⟨F, w', fun x => (hw x).symm.trans ?_⟩)
      exact congrArg F (funext fun a => by simp only [Function.comp_apply, hw' a, Wire.elim_input]; rfl)

theorem hardAux {n k : ℕ} (T : (Fin n → Bool) → Bool) (F : (Fin k → Bool) → Bool) (w : Fin k → Fin n)
    (hF : ∀ x, T x = F (x ∘ w)) (m : Fin n) (hm : ∀ a, w a ≠ m)
    (hT : T (fun _ => true) ≠ T (fun i => decide (i ≠ m))) : False :=
  hT ((hF _).trans ((congrArg F (funext fun a => by simp [hm a])).trans (hF _).symm))

theorem and2Hard : ¬ ((∃ i, ∀ x : Fin 2 → Bool, (x 0 && x 1) = x i) ∨ (∃ b, ∀ x : Fin 2 → Bool, (x 0 && x 1) = b) ∨
    (∃ (F : (Fin 1 → Bool) → Bool) (w : Fin 1 → Fin 2), ∀ x : Fin 2 → Bool, (x 0 && x 1) = F (x ∘ w))) := by
  rintro (⟨i, hi⟩ | ⟨b, hb⟩ | ⟨F, w, hF⟩)
  · have := hi (fun j => decide (j = i))
    fin_cases i <;> exact absurd this (by decide)
  · have h1 := hb (fun _ => true); have h2 := hb (fun _ => false)
    simp at h1 h2; simp_all
  · have key : ∀ p : Fin 2, ∃ m : Fin 2, p ≠ m := by decide
    obtain ⟨m, hm⟩ := key (w 0)
    exact hardAux _ F w hF m (fun a => by fin_cases a; exact hm) (by fin_cases m <;> decide)

theorem and3Hard : ¬ ((∃ i, ∀ x : Fin 3 → Bool, (x 0 && x 1 && x 2) = x i) ∨
    (∃ b, ∀ x : Fin 3 → Bool, (x 0 && x 1 && x 2) = b) ∨
    (∃ (F : (Fin 2 → Bool) → Bool) (w : Fin 2 → Fin 3), ∀ x : Fin 3 → Bool, (x 0 && x 1 && x 2) = F (x ∘ w))) := by
  rintro (⟨i, hi⟩ | ⟨b, hb⟩ | ⟨F, w, hF⟩)
  · have := hi (fun j => decide (j = i))
    fin_cases i <;> exact absurd this (by decide)
  · have h1 := hb (fun _ => true); have h2 := hb (fun _ => false)
    simp at h1 h2; simp_all
  · have key : ∀ p q : Fin 3, ∃ m : Fin 3, p ≠ m ∧ q ≠ m := by decide
    obtain ⟨m, h1, h2⟩ := key (w 0) (w 1)
    exact hardAux _ F w hF m (fun a => by fin_cases a <;> assumption) (by fin_cases m <;> decide)
end W2c0


namespace W2c0
-- free ternary terms: chains of ternary gates compute pairwise distinct functions
inductive Tm
  | var : ℕ → Tm
  | node : Tm → Tm → Tm → Tm
abbrev tS : Signature := ⟨Unit, fun _ => 3⟩
def tI : Interpretation tS Tm := fun _ x => .node (x 0) (x 1) (x 2)
def lastW {n : ℕ} (h0 : 0 < n) : (l : List (Fin n × Fin n)) → Wire n l.length
  | [] => .input ⟨0, h0⟩
  | _ :: l => .gate (Fin.last l.length)
def chain {n : ℕ} (h0 : 0 < n) : (l : List (Fin n × Fin n)) → Program tS n l.length
  | [] => .empty
  | p :: l => .gate (chain h0 l) ⟨(), ![lastW h0 l, .input p.1, .input p.2]⟩
def tmOf {n : ℕ} (h0 : 0 < n) (x : Fin n → Tm) : List (Fin n × Fin n) → Tm
  | [] => x ⟨0, h0⟩
  | p :: l => .node (tmOf h0 x l) (x p.1) (x p.2)
theorem chain_trace {n : ℕ} (h0 : 0 < n) (x : Fin n → Tm) :
    ∀ l, (chain h0 l).trace tI x (lastW h0 l) = tmOf h0 x l
  | [] => rfl
  | p :: l => by
    have ih := chain_trace h0 x l
    simp only [chain, lastW, Program.trace, Wire.elim_gate, Program.eval_gate_last, Line.eval, tmOf]
    simp only [Program.trace] at ih
    rw [← ih]; rfl
theorem tmOf_inj {n : ℕ} (h0 : 0 < n) :
    ∀ l₁ l₂ : List (Fin n × Fin n), l₁.length = l₂.length →
      tmOf h0 (fun i => .var i) l₁ = tmOf h0 (fun i => .var i) l₂ → l₁ = l₂
  | [], [], _, _ => rfl
  | p :: l₁, q :: l₂, hl, h => by
    simp only [tmOf, Tm.node.injEq, Tm.var.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    rw [tmOf_inj h0 l₁ l₂ (by simpa using hl) h1, Prod.ext (Fin.ext h2) (Fin.ext h3)]
theorem chain_count {n s : ℕ} (h0 : 0 < n) : (n * n) ^ s ≤ (computableFunctions tI n s).card := by
  let F : (Fin s → Fin n × Fin n) → computableFunctions tI n s := fun v =>
    ⟨fun x => tmOf h0 x (List.ofFn v), mem_computableFunctions.mpr
      ⟨⟨chain h0 (List.ofFn v), fun _ => lastW h0 (List.ofFn v)⟩,
        fun x => funext fun _ => chain_trace h0 x _, by simp⟩⟩
  have hF : Function.Injective F := fun v w h => by
    have := congrFun (congrArg Subtype.val h) (fun i => .var i)
    exact List.ofFn_injective (tmOf_inj h0 _ _ (by simp) this)
  have := Fintype.card_le_of_injective F hF
  simpa using this
end W2c0


-- `Cslib.Circuits.Interpretation.IsComplete.exists_computes_single` 3: necessary (empty signature, NOT)
theorem v0 : ¬ drop0% Cslib.Circuits.Interpretation.IsComplete.exists_computes_single 3 := fun h => by
  obtain ⟨c, hc⟩ := @h _ Bool emptyI 1 (fun x => !x 0)
  exact eNoNot c (hc.computesOn _)

-- `Cslib.Circuits.Interpretation.IsComplete.exists_computes` 3: necessary
theorem v1 : ¬ drop0% Cslib.Circuits.Interpretation.IsComplete.exists_computes 3 := fun h => by
  obtain ⟨c, hc⟩ := @h _ Bool emptyI 1 1 notF
  exact eNoNot c (hc.computesOn _)

-- `Cslib.Circuits.ecomplexityOn_le_of_computesOn` 8: necessary
theorem v2 : ¬ drop0% Cslib.Circuits.ecomplexityOn_le_of_computesOn 8 := fun h => by
  have := @h _ Bool 1 1 emptyI Set.univ notF (Circuit.id _ 1)
  rw [eTop] at this; simp at this

-- `Cslib.Circuits.exists_computesOn_size_eq_ecomplexityOn` 7: necessary
theorem v3 : ¬ drop0% Cslib.Circuits.exists_computesOn_size_eq_ecomplexityOn 7 := fun h => by
  obtain ⟨c, hc, -⟩ := @h _ Bool 1 1 emptyI Set.univ notF
  exact eNoNot c hc

-- `Cslib.Circuits.ecomplexityOn_mono` 8: necessary
theorem v4 : ¬ drop0% Cslib.Circuits.ecomplexityOn_mono 8 := fun h => by
  have := (@h _ Bool 1 1 emptyI Set.univ ∅ notF).trans
    (ecomplexityOn_le_of_computesOn (Circuit.id _ 1) (fun x hx => hx.elim))
  rw [eTop] at this; simp at this

-- `Cslib.Circuits.ecomplexityOn_congr` 8: necessary
theorem v5 : ¬ drop0% Cslib.Circuits.ecomplexityOn_congr 8 := fun h => by
  have := @h _ Bool 1 1 emptyI Set.univ notF (fun x => x ∘ id)
  rw [eTop, ecomplexityOn_wiring] at this; simp at this

-- `Cslib.Circuits.ecomplexity_le_of_computes` 7: necessary
theorem v6 : ¬ drop0% Cslib.Circuits.ecomplexity_le_of_computes 7 := fun h => by
  have := @h _ Bool 1 1 emptyI notF (Circuit.id _ 1)
  unfold ecomplexity at this; rw [eTop] at this; simp at this

-- `Cslib.Circuits.exists_computes_size_eq_ecomplexity` 6: necessary
theorem v7 : ¬ drop0% Cslib.Circuits.exists_computes_size_eq_ecomplexity 6 := fun h => by
  obtain ⟨c, hc, -⟩ := @h _ Bool 1 1 emptyI notF
  exact eNoNot c (hc.computesOn _)

-- `Cslib.Circuits.Synthesis.ecomplexity_le` 6: necessary
theorem v8 : ¬ drop0% Cslib.Circuits.Synthesis.ecomplexity_le 6 := fun h => by
  have := @h _ Bool 1 emptyI (fun x => !x 0) 0
  change ecomplexityOn emptyI Set.univ notF ≤ ((0 : ℕ) : ℕ∞) at this
  rw [eTop] at this; simp at this

-- `Cslib.Circuits.ecomplexityOn_ne_top` 7: necessary
theorem v9 : ¬ drop0% Cslib.Circuits.ecomplexityOn_ne_top 7 := fun h =>
  @h _ Bool 1 1 emptyI Set.univ notF eTop

-- `Cslib.Circuits.ecomplexity_ne_top` 6: necessary
theorem v10 : ¬ drop0% Cslib.Circuits.ecomplexity_ne_top 6 := fun h =>
  @h _ Bool 1 1 emptyI notF eTop

-- `Cslib.Circuits.natCast_complexityOn` 7: necessary
theorem v11 : ¬ indep0% Cslib.Circuits.natCast_complexityOn 7 := fun h =>
  emptySigNotComplete (@h _ Bool 0 0 emptyI ∅ (fun _ _ => true))

-- `Cslib.Circuits.natCast_complexity` 6: necessary
theorem v12 : ¬ indep0% Cslib.Circuits.natCast_complexity 6 := fun h =>
  emptySigNotComplete (@h _ Bool 0 0 emptyI (fun _ _ => true))

-- `Cslib.Circuits.complexityOn_le_of_computesOn` 7: necessary
theorem v13 : ¬ indep0% Cslib.Circuits.complexityOn_le_of_computesOn 7 := fun h =>
  emptySigNotComplete (@h _ Bool 0 0 emptyI ∅ (fun _ _ => true) (Circuit.id _ 0) (fun _ hx => hx.elim))

-- `Cslib.Circuits.complexityOn_le_of_computesOn` 9: necessary (De Morgan basis, NOT, identity circuit)
theorem v14 : ¬ drop0% Cslib.Circuits.complexityOn_le_of_computesOn 9 := fun h => by
  have := bNot.trans (@h _ Bool 1 1 BI Set.univ notF _ (Circuit.id _ 1))
  simp at this

-- `Cslib.Circuits.exists_computesOn_size_eq_complexityOn` 7: necessary
theorem v15 : ¬ indep0% Cslib.Circuits.exists_computesOn_size_eq_complexityOn 7 := fun h =>
  emptySigNotComplete (@h _ Bool 0 0 emptyI ∅ (fun _ _ => true))

-- `Cslib.Circuits.complexityOn_le_iff` 8: necessary
theorem v16 : ¬ indep0% Cslib.Circuits.complexityOn_le_iff 8 := fun h =>
  emptySigNotComplete (@h _ Bool 0 0 emptyI ∅ (fun _ _ => true) 0)

-- `Cslib.Circuits.le_complexityOn_iff` 8: necessary
theorem v17 : ¬ indep0% Cslib.Circuits.le_complexityOn_iff 8 := fun h =>
  emptySigNotComplete (@h _ Bool 0 0 emptyI ∅ (fun _ _ => true) 0)

-- `Cslib.Circuits.complexity_le_of_computes` 6: necessary
theorem v18 : ¬ indep0% Cslib.Circuits.complexity_le_of_computes 6 := fun h =>
  emptySigNotComplete (@h _ Bool 0 0 emptyI (fun _ _ => true) (Circuit.id _ 0)
    (fun _ => funext fun i => i.elim0))

-- `Cslib.Circuits.le_size_of_le_complexity` 7: necessary
theorem v19 : ¬ indep0% Cslib.Circuits.le_size_of_le_complexity 7 := fun h =>
  emptySigNotComplete (@h _ Bool 0 0 emptyI (fun _ _ => true) 0 (Circuit.id _ 0)
    (fun _ => funext fun i => i.elim0))

-- `Cslib.Circuits.le_size_of_le_complexity` 8: necessary (k = 1, identity circuit)
theorem v20 : ¬ drop0% Cslib.Circuits.le_size_of_le_complexity 8 := fun h => by
  have := @h _ Bool 1 1 BI (fun x => x ∘ id) 1 _ (Circuit.id _ 1) (Circuit.wiring_computes _ _)
  simp at this

-- `Cslib.Circuits.complexity_le_iff` 7: necessary
theorem v21 : ¬ indep0% Cslib.Circuits.complexity_le_iff 7 := fun h =>
  emptySigNotComplete (@h _ Bool 0 0 emptyI (fun _ _ => true) 0)

-- `Cslib.Circuits.le_complexity_iff` 7: necessary
theorem v22 : ¬ indep0% Cslib.Circuits.le_complexity_iff 7 := fun h =>
  emptySigNotComplete (@h _ Bool 0 0 emptyI (fun _ _ => true) 0)

-- `Cslib.Circuits.complexityOn_mono` 8: necessary
theorem v23 : ¬ indep0% Cslib.Circuits.complexityOn_mono 8 := fun h =>
  emptySigNotComplete (@h _ Bool 0 0 emptyI ∅ ∅ (fun _ _ => true) le_rfl)

-- `Cslib.Circuits.complexityOn_mono` 9: necessary
theorem v24 : ¬ drop0% Cslib.Circuits.complexityOn_mono 9 := fun h => by
  have := (bNot.trans (@h _ Bool 1 1 BI Set.univ ∅ notF _)).trans
    (complexityOn_le_of_computesOn (Circuit.id _ 1) (fun x hx => hx.elim))
  simp at this

-- `Cslib.Circuits.complexityOn_congr` 8: necessary
theorem v25 : ¬ indep0% Cslib.Circuits.complexityOn_congr 8 := fun h =>
  emptySigNotComplete (@h _ Bool 0 0 emptyI ∅ (fun _ _ => true) (fun _ _ => true) (fun _ hx => hx.elim))

-- `Cslib.Circuits.complexityOn_congr` 9: necessary
theorem v26 : ¬ drop0% Cslib.Circuits.complexityOn_congr 9 := fun h => by
  have := bNot
  rw [@h _ Bool 1 1 BI Set.univ notF (fun x => x ∘ id) _, complexityOn_wiring] at this
  simp at this

-- `Cslib.Circuits.complexityOn_wiring` 6: necessary
theorem v27 : ¬ indep0% Cslib.Circuits.complexityOn_wiring 6 := fun h =>
  emptySigNotComplete (@h _ Bool 0 0 emptyI ∅ id)

-- `Cslib.Circuits.complexityOn_comp_le` 7: necessary
theorem v28 : ¬ indep0% Cslib.Circuits.complexityOn_comp_le 7 := fun h =>
  emptySigNotComplete (@h _ Bool 0 0 0 emptyI ∅ (fun _ _ => true) (fun _ _ => true))

-- `Cslib.Circuits.complexityOn_append_le` 7: necessary
theorem v29 : ¬ indep0% Cslib.Circuits.complexityOn_append_le 7 := fun h =>
  emptySigNotComplete (@h _ Bool 0 0 0 emptyI ∅ (fun _ _ => true) (fun _ _ => true))

-- `Cslib.Circuits.complexityOn_le_complexityOn_append_left` 7: necessary
theorem v30 : ¬ indep0% Cslib.Circuits.complexityOn_le_complexityOn_append_left 7 := fun h =>
  emptySigNotComplete (@h _ Bool 0 0 0 emptyI ∅ (fun _ _ => true) (fun _ _ => true))

-- `Cslib.Circuits.complexityOn_le_complexityOn_append_right` 7: necessary
theorem v31 : ¬ indep0% Cslib.Circuits.complexityOn_le_complexityOn_append_right 7 := fun h =>
  emptySigNotComplete (@h _ Bool 0 0 0 emptyI ∅ (fun _ _ => true) (fun _ _ => true))

-- `Cslib.Circuits.complexity_wiring` 5: necessary
theorem v32 : ¬ indep0% Cslib.Circuits.complexity_wiring 5 := fun h =>
  emptySigNotComplete (@h _ Bool 0 0 emptyI id)

-- `Cslib.Circuits.complexity_comp_le` 6: necessary
theorem v33 : ¬ indep0% Cslib.Circuits.complexity_comp_le 6 := fun h =>
  emptySigNotComplete (@h _ Bool 0 0 0 emptyI (fun _ _ => true) (fun _ _ => true))

-- `Cslib.Circuits.complexity_append_le` 6: necessary
theorem v34 : ¬ indep0% Cslib.Circuits.complexity_append_le 6 := fun h =>
  emptySigNotComplete (@h _ Bool 0 0 0 emptyI (fun _ _ => true) (fun _ _ => true))

-- `Cslib.Circuits.complexity_le_complexity_append_left` 6: necessary
theorem v35 : ¬ indep0% Cslib.Circuits.complexity_le_complexity_append_left 6 := fun h =>
  emptySigNotComplete (@h _ Bool 0 0 0 emptyI (fun _ _ => true) (fun _ _ => true))

-- `Cslib.Circuits.complexity_le_complexity_append_right` 6: necessary
theorem v36 : ¬ indep0% Cslib.Circuits.complexity_le_complexity_append_right 6 := fun h =>
  emptySigNotComplete (@h _ Bool 0 0 0 emptyI (fun _ _ => true) (fun _ _ => true))

-- `Cslib.Circuits.Synthesis.complexity_le` 4: necessary (f = input projection, cost 0)
theorem v37 : ¬ indep0% Cslib.Circuits.Synthesis.complexity_le 4 := fun h =>
  emptySigNotComplete (@h _ Bool 1 emptyI (fun x => x 0) 0 (Synthesis.of_mem ⟨0, rfl⟩))

-- `Cslib.Circuits.Synthesis.complexity_le` 7: necessary
theorem v38 : ¬ drop0% Cslib.Circuits.Synthesis.complexity_le 7 := fun h => by
  have := @h _ Bool 1 BI _ (fun x => !x 0) 0
  change complexityOn BI Set.univ notF ≤ 0 at this
  have := bNot.trans this
  simp at this

-- `Cslib.Circuits.Circuit.Computes.comp` 10: necessary (identity circuits, f = NOT)
theorem v39 : ¬ drop0% Cslib.Circuits.Circuit.Computes.comp 10 := fun h => by
  have := congrFun (@h _ Bool 1 1 1 emptyI (Circuit.id _ 1) (Circuit.id _ 1) notF (fun x => x ∘ id)
    (Circuit.wiring_computes _ _) (fun _ => true)) 0
  simp [notF] at this

-- `Cslib.Circuits.Circuit.Computes.comp` 11: necessary (identity circuits, g = NOT)
theorem v40 : ¬ drop0% Cslib.Circuits.Circuit.Computes.comp 11 := fun h => by
  have := congrFun (@h _ Bool 1 1 1 emptyI (Circuit.id _ 1) (Circuit.id _ 1) (fun x => x ∘ id) notF
    (Circuit.wiring_computes _ _) (fun _ => true)) 0
  simp [notF] at this

-- `Cslib.Circuits.Circuit.Computes.append` 10: necessary
theorem v41 : ¬ drop0% Cslib.Circuits.Circuit.Computes.append 10 := fun h => by
  have := congrFun (@h _ Bool 1 1 1 emptyI (Circuit.id _ 1) (Circuit.id _ 1) notF (fun x => x ∘ id)
    (Circuit.wiring_computes _ _) (fun _ => true)) (Fin.castAdd 1 0)
  simp only [Circuit.eval_append, Fin.append_left] at this; simp [notF] at this

-- `Cslib.Circuits.Circuit.Computes.append` 11: necessary
theorem v42 : ¬ drop0% Cslib.Circuits.Circuit.Computes.append 11 := fun h => by
  have := congrFun (@h _ Bool 1 1 1 emptyI (Circuit.id _ 1) (Circuit.id _ 1) (fun x => x ∘ id) notF
    (Circuit.wiring_computes _ _) (fun _ => true)) (Fin.natAdd 1 0)
  simp only [Circuit.eval_append, Fin.append_right] at this; simp [notF] at this

-- `Cslib.Circuits.Circuit.ComputesOn.comp` 11: necessary
theorem v43 : ¬ drop0% Cslib.Circuits.Circuit.ComputesOn.comp 11 := fun h => by
  have := congrFun (@h _ Bool 1 1 1 emptyI (Circuit.id _ 1) (Circuit.id _ 1) Set.univ notF (fun x => x ∘ id)
    ((Circuit.wiring_computes _ _).computesOn _) (fun _ => true) (Set.mem_univ _)) 0
  simp [notF] at this

-- `Cslib.Circuits.Circuit.ComputesOn.comp` 12: necessary
theorem v44 : ¬ drop0% Cslib.Circuits.Circuit.ComputesOn.comp 12 := fun h => by
  have := congrFun (@h _ Bool 1 1 1 emptyI (Circuit.id _ 1) (Circuit.id _ 1) Set.univ (fun x => x ∘ id) notF
    ((Circuit.wiring_computes _ _).computesOn _) (fun _ => true) (Set.mem_univ _)) 0
  simp [notF] at this

-- `Cslib.Circuits.Circuit.ComputesOn.append` 11: necessary
theorem v45 : ¬ drop0% Cslib.Circuits.Circuit.ComputesOn.append 11 := fun h => by
  have := congrFun (@h _ Bool 1 1 1 emptyI (Circuit.id _ 1) (Circuit.id _ 1) Set.univ notF (fun x => x ∘ id)
    ((Circuit.wiring_computes _ _).computesOn _) (fun _ => true) (Set.mem_univ _)) (Fin.castAdd 1 0)
  simp only [Circuit.eval_append, Fin.append_left] at this; simp [notF] at this

-- `Cslib.Circuits.Circuit.ComputesOn.append` 12: necessary
theorem v46 : ¬ drop0% Cslib.Circuits.Circuit.ComputesOn.append 12 := fun h => by
  have := congrFun (@h _ Bool 1 1 1 emptyI (Circuit.id _ 1) (Circuit.id _ 1) Set.univ (fun x => x ∘ id) notF
    ((Circuit.wiring_computes _ _).computesOn _) (fun _ => true) (Set.mem_univ _)) (Fin.natAdd 1 0)
  simp only [Circuit.eval_append, Fin.append_right] at this; simp [notF] at this


-- `Cslib.Circuits.Interpretation.SimulatesWithCost.simulates` 6: necessary (empty basis does not simulate De Morgan)
theorem v109 : ¬ drop0% Cslib.Circuits.Interpretation.SimulatesWithCost.simulates 6 := fun h =>
  emptyNotSim (@h _ _ Bool BI emptyI (fun _ => 0))

-- `Cslib.Circuits.Program.cost_mono` 6: necessary (one gate, cost 1 vs 0)
theorem v110 : ¬ drop0% Cslib.Circuits.Program.cost_mono 6 := fun h => by
  have := @h uS 0 1 p1 (fun _ => 1) (fun _ => 0)
  simp [p1] at this

-- `Cslib.Circuits.Program.trace_simulate` 9: necessary (unary op: NOT under I, identity circuit over empty basis)
theorem v111 : ¬ drop0% Cslib.Circuits.Program.trace_simulate 9 := fun h => by
  have := congrFun (@h u1S ⟨Empty, Empty.elim⟩ Bool (fun _ x => !x 0) emptyI 1 1
    (.gate .empty ⟨(), fun _ => .input 0⟩) (fun _ => Circuit.id _ 1) (fun _ => true)) (.gate 0)
  exact absurd this (by decide +kernel)

-- `Cslib.Circuits.Program.exists_simulationWithCost` 9: necessary
theorem v112 : ¬ drop0% Cslib.Circuits.Program.exists_simulationWithCost 9 := fun h => by
  obtain ⟨k, q, ρ, -, hq⟩ := @h _ ⟨Empty, Empty.elim⟩ Bool BI emptyI 1 1 notC.program (fun _ => 0)
  rcases q with _ | ⟨q, ⟨op, _⟩⟩
  · have := congrFun (hq (fun _ => true)) (.gate 0)
    simp only [Function.comp_apply, Wire.Renaming.apply_gate] at this
    generalize ρ.gates 0 = w at this
    cases w with
    | input i => exact absurd this (by fin_cases i; decide +kernel)
    | gate j => exact j.elim0
  · exact op.elim

-- `Cslib.Circuits.Program.exists_simulation` 8: necessary
theorem v113 : ¬ drop0% Cslib.Circuits.Program.exists_simulation 8 := fun h => by
  obtain ⟨k, q, ρ, hq⟩ := @h _ ⟨Empty, Empty.elim⟩ Bool BI emptyI 1 1 notC.program
  rcases q with _ | ⟨q, ⟨op, _⟩⟩
  · have := congrFun (hq (fun _ => true)) (.gate 0)
    simp only [Function.comp_apply, Wire.Renaming.apply_gate] at this
    generalize ρ.gates 0 = w at this
    cases w with
    | input i => exact absurd this (by fin_cases i; decide +kernel)
    | gate j => exact j.elim0
  · exact op.elim

-- `Cslib.Circuits.Circuit.exists_simulationWithCost` 9: necessary
theorem v114 : ¬ drop0% Cslib.Circuits.Circuit.exists_simulationWithCost 9 := fun h => by
  obtain ⟨d, hd, -⟩ := @h _ ⟨Empty, Empty.elim⟩ Bool BI emptyI 1 1 notC (fun _ => 0)
  exact eNoNot d (fun x _ => by rw [hd]; exact notC_computes x)

-- `Cslib.Circuits.Circuit.exists_simulation_le` 9: necessary
theorem v115 : ¬ drop0% Cslib.Circuits.Circuit.exists_simulation_le 9 := fun h => by
  obtain ⟨d, hd, -⟩ := @h _ ⟨Empty, Empty.elim⟩ Bool BI emptyI 1 1 notC 0
  exact eNoNot d (fun x _ => by rw [hd]; exact notC_computes x)

-- `Cslib.Circuits.Interpretation.SimulatesWithCost.trans` 9: necessary
theorem v116 : ¬ drop0% Cslib.Circuits.Interpretation.SimulatesWithCost.trans 9 := fun h =>
  emptyNotSim ⟨_, @h _ _ Bool BI BI _ emptyI 0 1 (Interpretation.SimulatesWithCost.refl BI)⟩

-- `Cslib.Circuits.Interpretation.SimulatesWithCost.trans` 10: necessary
theorem v117 : ¬ drop0% Cslib.Circuits.Interpretation.SimulatesWithCost.trans 10 := fun h =>
  emptyNotSim ⟨_, @h _ _ Bool BI emptyI _ emptyI 1 0 (Interpretation.SimulatesWithCost.refl emptyI)⟩

-- `Cslib.Circuits.Circuit.exists_simulation` 8: necessary
theorem v118 : ¬ drop0% Cslib.Circuits.Circuit.exists_simulation 8 := fun h => by
  obtain ⟨d, hd⟩ := @h _ ⟨Empty, Empty.elim⟩ Bool BI emptyI 1 1 notC
  exact eNoNot d (fun x _ => by rw [hd]; exact notC_computes x)

-- `Cslib.Circuits.Circuit.ComputesOn.simulation` 11: necessary
theorem v119 : ¬ drop0% Cslib.Circuits.Circuit.ComputesOn.simulation 11 := fun h => by
  obtain ⟨d, hd⟩ := @h _ ⟨Empty, Empty.elim⟩ Bool BI emptyI 1 1 notC Set.univ notF
    (notC_computes.computesOn _)
  exact eNoNot d hd

-- `Cslib.Circuits.Circuit.Computes.simulation` 9: necessary
theorem v120 : ¬ drop0% Cslib.Circuits.Circuit.Computes.simulation 9 := fun h => by
  obtain ⟨d, hd⟩ := @h _ _ Bool emptyI emptyI 1 1 (Circuit.id _ 1) notF
    (Interpretation.Simulates.refl _)
  exact eNoNot d (hd.computesOn _)

-- `Cslib.Circuits.Circuit.Computes.simulation` 10: necessary
theorem v121 : ¬ drop0% Cslib.Circuits.Circuit.Computes.simulation 10 := fun h => by
  obtain ⟨d, hd⟩ := @h _ ⟨Empty, Empty.elim⟩ Bool BI emptyI 1 1 notC notF notC_computes
  exact eNoNot d (hd.computesOn _)

-- `Cslib.Circuits.Interpretation.Simulates.trans` 7: necessary
theorem v122 : ¬ drop0% Cslib.Circuits.Interpretation.Simulates.trans 7 := fun h =>
  emptyNotSim (@h _ _ Bool BI BI _ emptyI (Interpretation.Simulates.refl BI))

-- `Cslib.Circuits.Interpretation.Simulates.trans` 8: necessary
theorem v123 : ¬ drop0% Cslib.Circuits.Interpretation.Simulates.trans 8 := fun h =>
  emptyNotSim (@h _ _ Bool BI emptyI _ emptyI (Interpretation.Simulates.refl emptyI))

-- `Cslib.Circuits.Interpretation.Simulates.isComplete` 5: necessary
theorem v124 : ¬ drop0% Cslib.Circuits.Interpretation.Simulates.isComplete 5 := fun h =>
  emptySigNotComplete (@h _ _ Bool BI emptyI _)

-- `Cslib.Circuits.Interpretation.Simulates.isComplete` 6: necessary
theorem v125 : ¬ drop0% Cslib.Circuits.Interpretation.Simulates.isComplete 6 := fun h =>
  emptySigNotComplete (@h _ _ Bool emptyI emptyI (Interpretation.Simulates.refl emptyI))

-- `Cslib.Circuits.Interpretation.IsComplete.simulates` 4: necessary
theorem v126 : ¬ drop0% Cslib.Circuits.Interpretation.IsComplete.simulates 4 := fun h =>
  emptyNotSim (@h _ _ Bool emptyI BI)

-- `Cslib.Circuits.Program.foldl_rel` 11: necessary (R false, empty program)
theorem v84 : ¬ drop0% Cslib.Circuits.Program.foldl_rel 11 := fun h =>
  @h uS 0 0 ℕ ℕ .empty (fun _ _ => False) (fun {_} a _ => a) (fun {_} a _ => a) 0 0 (fun _ h => h)

-- `Cslib.Circuits.Program.foldl_rel` 12: necessary (R = Eq, one gate, f adds 1)
theorem v85 : ¬ drop0% Cslib.Circuits.Program.foldl_rel 12 := fun h => by
  have := @h uS 0 1 ℕ ℕ p1 (· = ·) (fun {_} a _ => a + 1) (fun {_} a _ => a) 0 0 rfl
  simp [p1] at this

-- `Cslib.Circuits.Program.foldr_rel` 11: necessary
theorem v86 : ¬ drop0% Cslib.Circuits.Program.foldr_rel 11 := fun h =>
  @h uS 0 0 ℕ ℕ .empty (fun _ _ => False) (fun {_} _ a => a) (fun {_} _ a => a) 0 0 (fun _ h => h)

-- `Cslib.Circuits.Program.foldr_rel` 12: necessary
theorem v87 : ¬ drop0% Cslib.Circuits.Program.foldr_rel 12 := fun h => by
  have := @h uS 0 1 ℕ ℕ p1 (· = ·) (fun {_} _ a => a + 1) (fun {_} _ a => a) 0 0 rfl
  simp [p1] at this

-- `Cslib.Circuits.Line.eval_mapWires` 13: necessary (different inputs)
theorem v88 : ¬ drop0% Cslib.Circuits.Line.eval_mapWires 13 := fun h => by
  have := @h u1S 1 1 0 0 Bool ⟨(), fun _ => .input 0⟩ id (fun _ x => x 0) (fun _ => true) (fun _ => false)
    Fin.elim0 Fin.elim0
  exact absurd this (by decide +kernel)

-- `Cslib.Circuits.Line.eval_mapRenaming` 11: necessary (different gate values)
theorem v89 : ¬ drop0% Cslib.Circuits.Line.eval_mapRenaming 11 := fun h => by
  have := @h u1S 0 1 1 Bool ⟨(), fun _ => .gate 0⟩ Wire.Renaming.id (fun _ x => x 0) Fin.elim0
    (fun _ => true) (fun _ => false)
  exact absurd this (by decide +kernel)

-- `Cslib.Circuits.Program.eq_eval_of_forall_lines_eval` 8: necessary (arbitrary values)
theorem v90 : ¬ drop0% Cslib.Circuits.Program.eq_eval_of_forall_lines_eval 8 := fun h => by
  have := congrFun (@h uS 0 1 Bool p1 (fun _ _ => true) Fin.elim0 (fun _ => false)) 0
  exact absurd this (by decide +kernel)

-- `Cslib.Circuits.Homomorphism.ext` 7: necessary (identity and negation over the empty signature)
theorem v83 : ¬ drop0% Cslib.Circuits.Homomorphism.ext 7 := fun h => by
  have := congrFun (congrArg Homomorphism.map (@h ⟨Empty, Empty.elim⟩ Bool Bool emptyI emptyI
    ⟨id, fun op => op.elim⟩ ⟨not, fun op => op.elim⟩)) true
  simp at this


-- `Cslib.Circuits.mem_computableFunctions` 1: necessary (infinitely many operations)
theorem v47 : ¬ indep0% Cslib.Circuits.mem_computableFunctions 1 := fun h =>
  Infinite.not_finite (α := ℕ) (@h nS Bool (fun _ _ => true) 0 0 (fun _ => true))

-- `Cslib.Circuits.mem_computableFunctions_iff_ecomplexity_le` 1: necessary
theorem v48 : ¬ indep0% Cslib.Circuits.mem_computableFunctions_iff_ecomplexity_le 1 := fun h =>
  Infinite.not_finite (α := ℕ) (@h nS Bool (fun _ _ => true) 0 0 (fun _ => true))

-- `_private.Cslib.Computability.Circuit.Counting.0.Cslib.Circuits.mem_irredundantFunctions_iff` 1: necessary
theorem v49 : ¬ indep0% _private.Cslib.Computability.Circuit.Counting.«0».Cslib.Circuits.mem_irredundantFunctions_iff 1 := fun h =>
  Infinite.not_finite (α := ℕ) (@h nS Bool (fun _ _ => true) 0 0 (fun _ => true))

-- `Cslib.Circuits.mem_irredundantFunctions` 1: necessary
theorem v50 : ¬ indep0% Cslib.Circuits.mem_irredundantFunctions 1 := fun h =>
  Infinite.not_finite (α := ℕ) (@h nS Bool (fun _ _ => true) 0 0 (fun _ => true))

-- `_private.Cslib.Computability.Circuit.Counting.0.Cslib.Circuits.relabel_unique` 9: necessary (arbitrary gate values)
theorem v51 : ¬ drop0% _private.Cslib.Computability.Circuit.Counting.«0».Cslib.Circuits.relabel_unique 9 := fun h => by
  have := congrFun (@h uS Bool (fun _ _ => true) 0 1 (p1, .gate 0) (Equiv.refl _) Fin.elim0 (fun _ => false)) 0
  exact absurd this (by decide +kernel)

-- `_private.Cslib.Computability.Circuit.Counting.0.Cslib.Circuits.representative_spec` 1: necessary
theorem v52 : ¬ indep0% _private.Cslib.Computability.Circuit.Counting.«0».Cslib.Circuits.representative_spec 1 := fun h =>
  Infinite.not_finite (α := ℕ) (@h nS Bool (fun _ _ => true) 0 0)

-- `_private.Cslib.Computability.Circuit.Counting.0.Cslib.Circuits.relabel_injective` 1: necessary
theorem v53 : ¬ indep0% _private.Cslib.Computability.Circuit.Counting.«0».Cslib.Circuits.relabel_injective 1 := fun h =>
  Infinite.not_finite (α := ℕ) (@h nS Bool (fun _ _ => true) 0 0)

-- `Cslib.Circuits.card_irredundantFunctions_mul_factorial_le` 1: necessary
theorem v54 : ¬ indep0% Cslib.Circuits.card_irredundantFunctions_mul_factorial_le 1 := fun h =>
  Infinite.not_finite (α := ℕ) (@h nS Bool (fun _ _ => true) 0 0)

-- `Cslib.Circuits.card_computableFunctions_le_sum` 1: necessary
theorem v55 : ¬ indep0% Cslib.Circuits.card_computableFunctions_le_sum 1 := fun h =>
  Infinite.not_finite (α := ℕ) (@h nS Bool (fun _ _ => true) 0 0)

-- `Cslib.Circuits.card_computableFunctions_mul_factorial_le` 1: necessary (lines over nS are infinite)
theorem v56 : ¬ indep0% Cslib.Circuits.card_computableFunctions_mul_factorial_le 1 := fun h =>
  Infinite.not_finite (α := ℕ) (@h nS Bool (fun _ _ => true) 0 0 0 le_rfl
    (fun _ _ => (Nat.card_eq_zero_of_infinite).le))

-- `Cslib.Circuits.card_computableFunctions_mul_factorial_le` 7: necessary (empty signature, B = 0, s = 1)
theorem v57 : ¬ drop0% Cslib.Circuits.card_computableFunctions_mul_factorial_le 7 := fun h => by
  have := @h ⟨Empty, Empty.elim⟩ (inferInstanceAs (Finite Empty)) Bool emptyI 1 1 0
    (fun _ _ => (Nat.card_eq_zero.mpr (Or.inl ⟨fun l => l.op.elim⟩)).le)
  have hpos : 0 < (computableFunctions emptyI 1 1).card := Finset.card_pos.mpr
    ⟨fun x => x 0, mem_computableFunctions.mpr
      ⟨Circuit.wiring _ (fun _ => 0), fun _ => funext fun _ => rfl, by simp⟩⟩
  have e : (1 + 1) * 0 ^ 1 * (1 + 1) = 0 := rfl
  rw [e, Nat.factorial_one, mul_one] at this; omega

-- `Cslib.Circuits.card_computableFunctions_mul_factorial_le` 8: necessary (binary op x ∧ ¬y, n = 3, s = B = 1)
theorem v58 : ¬ drop0% Cslib.Circuits.card_computableFunctions_mul_factorial_le 8 := fun h => by
  have := @h aS (inferInstanceAs (Finite Unit)) Bool aI 3 1 1 le_rfl
  have := nine
  simp at *; omega

-- `Cslib.Circuits.card_computableFunctions_mul_factorial_le_of_arity_le` 1: necessary
theorem v59 : ¬ indep0% Cslib.Circuits.card_computableFunctions_mul_factorial_le_of_arity_le 1 := fun h =>
  Infinite.not_finite (α := ℕ) (@h nS Bool (fun _ _ => true) 0 0 0 (fun _ => le_rfl))

-- `Cslib.Circuits.card_computableFunctions_mul_factorial_le_of_arity_le` 7: necessary (binary op, r = 0)
theorem v60 : ¬ drop0% Cslib.Circuits.card_computableFunctions_mul_factorial_le_of_arity_le 7 := fun h => by
  have := @h aS (inferInstanceAs (Finite Unit)) Bool aI 3 1 0
  have := nine
  simp at *; omega

-- `Cslib.Circuits.Line.instFinite` 1: necessary
theorem v61 : ¬ drop0% Cslib.Circuits.Line.instFinite 1 := fun h =>
  Infinite.not_finite (@h nS 0 0)

-- `Cslib.Circuits.Program.instFinite` 1: necessary
theorem v62 : ¬ drop0% Cslib.Circuits.Program.instFinite 1 := fun h => by
  have : Infinite (Program nS 0 1) := Infinite.of_injective
    (fun k : ℕ => Program.gate .empty (⟨k, Fin.elim0⟩ : Line nS 0 0))
    (fun _ _ h => congrArg (fun p => ((Program.gateEquiv nS 0 0) p).2.op) h)
  exact Infinite.not_finite (@h nS 0 1)

-- `Cslib.Circuits.Line.card_le` 5: necessary (one binary op, two wires, r = 0)
theorem v65 : ¬ drop0% Cslib.Circuits.Line.card_le 5 := fun h => by
  have := @h aS (inferInstanceAs (Finite Unit)) 2 0 0
  rw [Line.card, finsum_eq_sum_of_fintype] at this
  simp at this

-- `Cslib.Circuits.FullOp.instFinite` 1: necessary (U = ℕ)
theorem v67 : ¬ drop0% Cslib.Circuits.FullOp.instFinite 1 := fun h => by
  have : Infinite (FullOp 0 ℕ) := Infinite.of_injective FullOp.con (fun _ _ h => by cases h; rfl)
  exact Infinite.not_finite (@h ℕ 0)

-- `Cslib.Circuits.FullOp.card` 2: necessary (U = ℕ, k = 1)
theorem v68 : ¬ drop0% Cslib.Circuits.FullOp.card 2 := fun h => by
  have : Infinite (FullOp 1 ℕ) := Infinite.of_injective FullOp.con (fun _ _ h => by cases h; rfl)
  have := @h 1 ℕ
  simp [Nat.card_eq_zero_of_infinite] at this

-- `Cslib.Circuits.instFiniteOpFullSignature` 1: necessary
theorem v69 : ¬ drop0% Cslib.Circuits.instFiniteOpFullSignature 1 := fun h => by
  have : Infinite (FullOp 0 ℕ) := Infinite.of_injective FullOp.con (fun _ _ h => by cases h; rfl)
  exact Infinite.not_finite (α := FullOp 0 ℕ) (@h ℕ 0)

-- `Cslib.Circuits.Line.card_full` 4: necessary (U = ℕ, k = n = 1, g = 0)
theorem v70 : ¬ drop0% Cslib.Circuits.Line.card_full 4 := fun h => by
  have : Infinite (Line (fullSignature 1 ℕ) 1 0) := Infinite.of_injective
    (fun k : ℕ => (⟨FullOp.con k, Fin.elim0⟩ : Line (fullSignature 1 ℕ) 1 0))
    (fun a b h => by have := congrArg Line.op h; cases this; rfl)
  have := @h 1 1 0 ℕ
  simp [Nat.card_eq_zero_of_infinite] at this

-- `Cslib.Circuits.ecomplexityGiven_le_of_eval` 9: necessary (empty signature, NOT given nothing)
theorem v91 : ¬ drop0% Cslib.Circuits.ecomplexityGiven_le_of_eval 9 := fun h => by
  have := @h _ Bool 1 1 0 emptyI notF (fun _ => Fin.elim0) (Circuit.id _ (1 + 0))
  obtain ⟨c, hc, -⟩ := (ecomplexityGiven_le_iff (s := 0) _ _).mp this
  exact eNoNot c (fun x _ => by simpa [Fin.append_elim0] using hc x)

-- `Cslib.Circuits.ecomplexityGiven_ne_top` 6: necessary
theorem v92 : ¬ drop0% Cslib.Circuits.ecomplexityGiven_ne_top 6 := fun h => by
  have := @h _ Bool 1 1 0 emptyI notF (fun _ => Fin.elim0)
  obtain ⟨c, hc⟩ := ecomplexityOn_ne_top_iff.mp this
  have hc := c.computesOn_graph_iff.mp hc
  exact eNoNot c (fun x _ => by simpa [Fin.append_elim0] using hc x)

-- `Cslib.Circuits.natCast_complexityGiven` 6: necessary
theorem v93 : ¬ indep0% Cslib.Circuits.natCast_complexityGiven 6 := fun h =>
  emptySigNotComplete (@h _ Bool 0 0 0 emptyI (fun _ _ => true) (fun _ _ => true))

-- `Cslib.Circuits.complexityGiven_self` 5: necessary
theorem v94 : ¬ indep0% Cslib.Circuits.complexityGiven_self 5 := fun h =>
  emptySigNotComplete (@h _ Bool 0 0 emptyI (fun _ _ => true))

-- `Cslib.Circuits.complexityGiven_le_complexity` 6: necessary
theorem v95 : ¬ indep0% Cslib.Circuits.complexityGiven_le_complexity 6 := fun h =>
  emptySigNotComplete (@h _ Bool 0 0 0 emptyI (fun _ _ => true) (fun _ _ => true))

-- `Cslib.Circuits.complexity_le_add_complexityGiven` 6: necessary
theorem v96 : ¬ indep0% Cslib.Circuits.complexity_le_add_complexityGiven 6 := fun h =>
  emptySigNotComplete (@h _ Bool 0 0 0 emptyI (fun _ _ => true) (fun _ _ => true))

-- `Cslib.Circuits.complexity_append_le_add_complexityGiven` 6: necessary
theorem v97 : ¬ indep0% Cslib.Circuits.complexity_append_le_add_complexityGiven 6 := fun h =>
  emptySigNotComplete (@h _ Bool 0 0 0 emptyI (fun _ _ => true) (fun _ _ => true))

-- `Cslib.Circuits.complexityGiven_le_add` 7: necessary
theorem v98 : ¬ indep0% Cslib.Circuits.complexityGiven_le_add 7 := fun h =>
  emptySigNotComplete (@h _ Bool 0 0 0 0 emptyI (fun _ _ => true) (fun _ _ => true) (fun _ _ => true))

-- `Cslib.Circuits.complexityGiven_append_le` 7: necessary
theorem v99 : ¬ indep0% Cslib.Circuits.complexityGiven_append_le 7 := fun h =>
  emptySigNotComplete (@h _ Bool 0 0 0 0 emptyI (fun _ _ => true) (fun _ _ => true) (fun _ _ => true))

-- `_private.Cslib.Computability.Circuit.Shannon.0.Cslib.Circuits.Shannon.exists_card_le_exp` 2: necessary
theorem v100 : ¬ indep0% _private.Cslib.Computability.Circuit.Shannon.«0».Cslib.Circuits.Shannon.exists_card_le_exp 2 := fun h =>
  Infinite.not_finite (α := ℕ) (@h nS Bool (fun _ _ => true) (fun _ => by simp))

-- `_private.Cslib.Computability.Circuit.Shannon.0.Cslib.Circuits.Shannon.eventually_card_lt` 2: necessary
theorem v102 : ¬ indep0% _private.Cslib.Computability.Circuit.Shannon.«0».Cslib.Circuits.Shannon.eventually_card_lt 2 := fun h =>
  Infinite.not_finite (α := ℕ) (@h nS Bool _ _ (fun _ _ => true) (fun _ => by simp))

-- `_private.Cslib.Computability.Circuit.Shannon.0.Cslib.Circuits.Shannon.eventually_card_lt` 4: necessary (U = Unit: one function, one projection)
theorem v103 : ¬ drop0% _private.Cslib.Computability.Circuit.Shannon.«0».Cslib.Circuits.Shannon.eventually_card_lt 4 := fun h => by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (@h ⟨Empty, Empty.elim⟩ Unit (inferInstanceAs (Finite Empty)) _ eIU (fun op => op.elim))
  have := hN (N + 1) (by omega)
  have hpos : 0 < (computableFunctions eIU (N + 1)
      (Fintype.card Unit ^ (N + 1) / (N + 1))).card := Finset.card_pos.mpr
    ⟨fun x => x 0, mem_computableFunctions.mpr
      ⟨Circuit.wiring _ (fun _ => 0), fun _ => funext fun _ => rfl, by simp⟩⟩
  simp only [Fintype.card_unit, one_pow] at this hpos
  omega

-- `Cslib.Circuits.Shannon.exists_hard_function` 4: necessary (U = Unit: the projection computes everything)
theorem v107 : ¬ drop0% Cslib.Circuits.Shannon.exists_hard_function 4 := fun h => by
  obtain ⟨N, hN⟩ := @h ⟨Empty, Empty.elim⟩ Unit (inferInstanceAs (Finite Empty)) _ eIU
    (fun op => op.elim)
  obtain ⟨f, hf⟩ := hN (N + 1) (by omega)
  have := hf (Circuit.wiring _ (fun _ => 0)) (fun _ => funext fun _ => rfl)
  simp at this
  have : (0 : ℝ) < (N + 1 : ℝ)⁻¹ := by positivity
  linarith


-- `Cslib.Circuits.Line.card` 1: removable (if the sigma type is infinite, so is the support of the finsum; both sides are then 0)
theorem v63 : drop% Cslib.Circuits.Line.card 1 := fun n g => lineCard n g

-- `Cslib.Circuits.Program.card` 1: removable (product of line counts; Line.card holds without finiteness)
theorem v66 : drop% Cslib.Circuits.Program.card 1 := fun n g => progCard n g

-- `Cslib.Circuits.Line.card_le` 1: necessary (ops ℕ, only op 0 nullary, no wires: one line, Nat.card ℕ = 0)
theorem v64 : ¬ drop0% Cslib.Circuits.Line.card_le 1 := fun h => by
  have := @h ⟨ℕ, ar1⟩ 0 0 1 (fun k => by cases k <;> simp [ar1])
  rw [lineCard, finsum_eq_single _ 0 (fun k hk => by cases k; exact absurd rfl hk; rfl),
    Nat.card_eq_zero_of_infinite] at this
  simp [ar1] at this

-- `_private.Cslib.Computability.Circuit.Full.0.Cslib.Circuits.fullInterpretation_isComplete_two` 1: removable (on an infinite carrier, pair the inputs injectively with U × U ≃ U, then one gate decodes)
theorem v79 : drop% _private.Cslib.Computability.Circuit.Full.«0».Cslib.Circuits.fullInterpretation_isComplete_two 1 :=
  fun {U} => complete2 U

-- `Cslib.Circuits.fullInterpretation_isComplete` 2: removable (the binary full basis is complete on every carrier)
theorem v80 : drop% Cslib.Circuits.fullInterpretation_isComplete 2 := by
  intro U k hk
  have := complete2 U
  exact (fullInterpretation_simulates (fullInterpretation (k := 2) (Carrier := U))
    (by rintro (_ | _) <;> simp [fullSignature, hk])).isComplete

-- `Cslib.Circuits.instIsCompleteFullInterpretation` 2: removable (same argument)
theorem v82 : drop% Cslib.Circuits.instIsCompleteFullInterpretation 2 := by
  intro U k
  have := complete2 U
  exact (fullInterpretation_simulates (fullInterpretation (k := 2) (Carrier := U))
    (by rintro (_ | _) <;> simp [fullSignature])).isComplete

-- `Cslib.Circuits.fullInterpretation_isComplete` 3: necessary (k = 0: only constants)
theorem v81 : ¬ drop0% Cslib.Circuits.fullInterpretation_isComplete 3 := fun h => by
  obtain ⟨c, hc⟩ := (@h Bool 0 _).exists_computes_single (fun x : Fin 1 → Bool => !x 0)
  exact notFull0 c hc

-- `Cslib.Circuits.fullInterpretation_simulatesWithCost` 4: necessary (k = 0 cannot simulate NOT)
theorem v77 : ¬ drop0% Cslib.Circuits.fullInterpretation_simulatesWithCost 4 := fun h => by
  obtain ⟨c, hc, -⟩ := @h Bool 0 u1S (fun _ x => !x 0) ()
  exact notFull0 c hc

-- `Cslib.Circuits.fullInterpretation_simulates` 4: necessary
theorem v78 : ¬ drop0% Cslib.Circuits.fullInterpretation_simulates 4 := fun h => by
  obtain ⟨_, hcost⟩ := @h Bool 0 u1S (fun _ x => !x 0)
  obtain ⟨c, hc, -⟩ := hcost ()
  exact notFull0 c hc

-- `Cslib.Circuits.Synthesis.full_gate` 5: necessary (k = 0, r = 1, NOT of the input)
theorem v71 : ¬ drop0% Cslib.Circuits.Synthesis.full_gate 5 := fun h => by
  obtain ⟨c, hc, -⟩ := (@h Bool 0 1 (inputs 1) 1 (fun v => !v 0) (fun _ x => x 0)
    (fun _ => ⟨0, rfl⟩)).exists_circuit
  exact notFull0 c hc

-- `Cslib.Circuits.Synthesis.full_gate_of_syntheses` 5: necessary (same, costs 0)
theorem v73 : ¬ drop0% Cslib.Circuits.Synthesis.full_gate_of_syntheses 5 := fun h => by
  obtain ⟨c, hc, -⟩ := (@h Bool 0 1 (inputs 1) 1 (fun v => !v 0) (fun _ x => x 0) (fun _ => 0)
    (fun _ => Synthesis.of_mem ⟨0, rfl⟩)).exists_circuit
  exact notFull0 c hc

-- `Cslib.Circuits.Shannon.exists_hard_function` 2: removable (simulate by the finite binary full basis, one gate per gate)
theorem v105 : drop% Cslib.Circuits.Shannon.exists_hard_function 2 := by
  intro σ U _ _ I harity
  obtain ⟨N, hN⟩ := Shannon.exists_hard_function (fullInterpretation (k := 2) (Carrier := U))
    (by rintro (_ | _) <;> simp [fullSignature])
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨f, hf⟩ := hN n hn
  refine ⟨f, fun c hc => ?_⟩
  obtain ⟨d, hd, hsize⟩ := c.exists_simulation_le (fullInterpretation_simulatesWithCost I harity)
  have h1 := hf d (fun x => (congrFun hd x).trans (hc x))
  have h2 : (d.size : ℝ) ≤ c.size := by exact_mod_cast (by simpa using hsize)
  linarith

-- `Cslib.Circuits.Shannon.exists_hard_function` 3: removable (infinite U: Nat.card U = 0, and a constant needs a gate)
theorem v106 : drop% Cslib.Circuits.Shannon.exists_hard_function 3 := by
  intro σ U _ _ I harity
  by_cases hU : Finite U
  · exact Shannon.exists_hard_function I harity
  have : Infinite U := not_finite_iff_infinite.mp hU
  obtain ⟨a, b, hab⟩ := exists_pair_ne U
  refine ⟨1, fun n hn => ⟨fun _ => a, fun c hc => ?_⟩⟩
  rw [Nat.card_eq_zero_of_infinite, Nat.cast_zero, zero_pow (by omega), zero_div]
  rcases Nat.eq_zero_or_pos c.size with h0 | hpos
  · obtain ⟨i, hi⟩ := size0proj I c h0
    have := (hi (fun _ => b)).symm.trans (congrFun (hc (fun _ => b)) 0)
    exact absurd ((this : b = a).symm) hab
  · exact_mod_cast hpos


-- `Cslib.Circuits.Synthesis.full_gate` 8: necessary (k = r = 1, argument x0 ∧ x1 not available: one unary gate cannot compute it)
theorem v72 : ¬ drop0% Cslib.Circuits.Synthesis.full_gate 8 := fun h =>
  and2Hard (oneGate _ (@h Bool 1 2 (inputs 2) 1 le_rfl (fun v => v 0) (fun _ x => x 0 && x 1)) le_rfl)

-- `Cslib.Circuits.Synthesis.full_gate_of_syntheses` 9: necessary (same, costs 0)
theorem v74 : ¬ drop0% Cslib.Circuits.Synthesis.full_gate_of_syntheses 9 := fun h =>
  and2Hard (oneGate _ (@h Bool 1 2 (inputs 2) 1 le_rfl (fun v => v 0) (fun _ x => x 0 && x 1) (fun _ => 0))
    (by simp))

-- `Cslib.Circuits.Synthesis.full_binary` 7: necessary (f = x0 ∧ x1 ∧ x2 needs two binary gates, g = x0, a = b = 0)
theorem v75 : ¬ drop0% Cslib.Circuits.Synthesis.full_binary 7 := fun h =>
  and3Hard (oneGate _ (@h Bool 3 0 0 (inputs 3) (fun x => x 0 && x 1 && x 2) (fun x => x 0)
    (Synthesis.of_mem ⟨0, rfl⟩) (fun u _ => u)) le_rfl)

-- `Cslib.Circuits.Synthesis.full_binary` 8: necessary (symmetric)
theorem v76 : ¬ drop0% Cslib.Circuits.Synthesis.full_binary 8 := fun h =>
  and3Hard (oneGate _ (@h Bool 3 0 0 (inputs 3) (fun x => x 0) (fun x => x 0 && x 1 && x 2)
    (Synthesis.of_mem ⟨0, rfl⟩) (fun _ v => v)) le_rfl)


-- `_private.Cslib.Computability.Circuit.Shannon.0.Cslib.Circuits.Shannon.exists_card_le_exp` 4: necessary (one free ternary operation: chains of s gates on n = s - 1 inputs give ((s-1)^2)^s distinct functions)
theorem v101 : ¬ drop0% _private.Cslib.Computability.Circuit.Shannon.«0».Cslib.Circuits.Shannon.exists_card_le_exp 4 := fun h => by
  obtain ⟨C, hC⟩ := @h tS Tm (inferInstanceAs (Finite Unit)) tI
  set s : ℕ := ⌈Real.exp C⌉₊ + 3 with hs
  have hcount := chain_count (n := s - 1) (s := s) (by omega)
  have hle := hC (s - 1) s (by omega)
  have hs1 : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hspos : (0 : ℝ) < s := by positivity
  have hexp : Real.exp (s * Real.log s + C * s) = (s * Real.exp C) ^ s := by
    rw [show (s : ℝ) * Real.log s + C * s = ((s : ℕ) : ℝ) * (Real.log s + C) by ring,
      Real.exp_nat_mul, Real.exp_add, Real.exp_log hspos]
  have hceil : Real.exp C ≤ (⌈Real.exp C⌉₊ : ℝ) := Nat.le_ceil _
  have hsr : (s : ℝ) = (⌈Real.exp C⌉₊ : ℝ) + 3 := by rw [hs]; push_cast; ring
  have hlt : (s : ℝ) * Real.exp C < ((s : ℝ) - 1) * ((s : ℝ) - 1) := by
    have : (s : ℝ) * Real.exp C ≤ (s : ℝ) * ((s : ℝ) - 3) :=
      mul_le_mul_of_nonneg_left (by linarith) hspos.le
    nlinarith
  have hpow : ((s : ℝ) * Real.exp C) ^ s < (((s : ℝ) - 1) * ((s : ℝ) - 1)) ^ s :=
    pow_lt_pow_left₀ hlt (by positivity) (by omega)
  have hc : (((s - 1) * (s - 1)) ^ s : ℕ) ≤ ((computableFunctions tI (s - 1) s).card : ℝ) := by
    exact_mod_cast hcount
  push_cast [hs1] at hc
  rw [hexp] at hle
  linarith
