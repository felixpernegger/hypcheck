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

namespace W1c5
open Cslib Logic.Modal

abbrev τU : PFunctor := PFunctor.mkUnary Unit
abbrev τB : PFunctor := PFunctor.mkUnary Bool

def BM0 : BTL.Model Unit Unit := ⟨fun _ _ => False, fun _ _ => False⟩
def BM1 : BTL.Model Unit Unit := ⟨fun _ _ => True, fun _ _ => False⟩

-- `Cslib.Logic.Modal.Satisfies.btl_future_sometime_intro` idx 6: necessary (empty relation, φ = ⊤)
theorem b1 : ¬ drop0% Cslib.Logic.Modal.Satisfies.btl_future_sometime_intro 6 := fun h => by
  obtain ⟨_, h1, _⟩ := Satisfies.btl_future_sometime_iff.mp
    (@h Unit Unit BM0 () () Logic.Modal.Proposition.true Satisfies.true)
  exact h1

-- `Cslib.Logic.Modal.Satisfies.btl_future_sometime_intro` idx 7: necessary (total relation, φ = ⊥)
theorem b2 : ¬ drop0% Cslib.Logic.Modal.Satisfies.btl_future_sometime_intro 7 := fun h => by
  obtain ⟨_, _, h2⟩ := Satisfies.btl_future_sometime_iff.mp
    (@h Unit Unit BM1 () () Logic.Modal.Proposition.false trivial)
  exact h2

-- `Cslib.Logic.Modal.Satisfies.btl_past_sometime_intro` idx 6: necessary (empty relation, φ = ⊤)
theorem b3 : ¬ drop0% Cslib.Logic.Modal.Satisfies.btl_past_sometime_intro 6 := fun h => by
  obtain ⟨_, h1, _⟩ := Satisfies.btl_past_sometime_iff.mp
    (@h Unit Unit BM0 () () Logic.Modal.Proposition.true Satisfies.true)
  exact h1

-- `Cslib.Logic.Modal.Satisfies.btl_past_sometime_intro` idx 7: necessary (total relation, φ = ⊥)
theorem b4 : ¬ drop0% Cslib.Logic.Modal.Satisfies.btl_past_sometime_intro 7 := fun h => by
  obtain ⟨_, _, h2⟩ := Satisfies.btl_past_sometime_iff.mp
    (@h Unit Unit BM1 () () Logic.Modal.Proposition.false trivial)
  exact h2

-- `Cslib.Logic.Modal.Satisfies.btl_future_always_elim` idx 6: necessary (total relation, φ = ⊥)
theorem b5 : ¬ drop0% Cslib.Logic.Modal.Satisfies.btl_future_always_elim 6 := fun h =>
  @h Unit Unit BM1 () () Logic.Modal.Proposition.false trivial

-- `Cslib.Logic.Modal.Satisfies.btl_future_always_elim` idx 7: necessary (empty relation, φ = ⊥)
theorem b6 : ¬ drop0% Cslib.Logic.Modal.Satisfies.btl_future_always_elim 7 := fun h =>
  @h Unit Unit BM0 () () Logic.Modal.Proposition.false
    (Satisfies.btl_future_always_iff.mpr fun _ h => h.elim)

-- `Cslib.Logic.Modal.Satisfies.btl_past_always_elim` idx 7: necessary (empty relation, φ = ⊥)
theorem b7 : ¬ drop0% Cslib.Logic.Modal.Satisfies.btl_past_always_elim 7 := fun h =>
  @h Unit Unit BM0 () () Logic.Modal.Proposition.false
    (Satisfies.btl_past_always_iff.mpr fun _ h => h.elim)

def HM0 : HML.Model Unit Unit Unit := ⟨⟨fun _ _ _ => False⟩, fun _ _ => False⟩
def HM1 : HML.Model Unit Unit Unit := ⟨⟨fun _ _ _ => True⟩, fun _ _ => False⟩

-- `Cslib.Logic.Modal.Satisfies.hml_dynDiamond_intro` idx 8: necessary (empty LTS, φ = ⊤)
theorem h1 : ¬ drop0% Cslib.Logic.Modal.Satisfies.hml_dynDiamond_intro 8 := fun h => by
  obtain ⟨_, h1, _⟩ := Satisfies.hml_dynDiamond_iff_exists.mp
    (@h Unit Unit Unit HM0 () () () Logic.Modal.Proposition.true Satisfies.true)
  exact h1

-- `Cslib.Logic.Modal.Satisfies.hml_dynDiamond_intro` idx 9: necessary (total LTS, φ = ⊥)
theorem h2 : ¬ drop0% Cslib.Logic.Modal.Satisfies.hml_dynDiamond_intro 9 := fun h => by
  obtain ⟨_, _, h2⟩ := Satisfies.hml_dynDiamond_iff_exists.mp
    (@h Unit Unit Unit HM1 () () () Logic.Modal.Proposition.false trivial)
  exact h2

-- `Cslib.Logic.Modal.Satisfies.hml_dynBox_elim` idx 8: necessary (total LTS, φ = ⊥)
theorem h3 : ¬ drop0% Cslib.Logic.Modal.Satisfies.hml_dynBox_elim 8 := fun h =>
  @h Unit Unit Unit HM1 () () Logic.Modal.Proposition.false () trivial

-- `Cslib.Logic.Modal.Satisfies.hml_dynBox_elim` idx 9: necessary (empty LTS, φ = ⊥)
theorem h4 : ¬ drop0% Cslib.Logic.Modal.Satisfies.hml_dynBox_elim 9 := fun h =>
  @h Unit Unit Unit HM0 () () Logic.Modal.Proposition.false ()
    (Satisfies.hml_dynBox_iff_forall.mpr fun _ h => h.elim)

end W1c5

namespace W1c5
open Cslib Logic.Modal

/-- states true/false, no transitions, atom true exactly at true -/
def HMv : HML.Model Bool Unit Unit := ⟨⟨fun _ _ _ => False⟩, fun s _ => s = true⟩
/-- states true/false, true → anything, no atoms -/
def HMt : HML.Model Bool Unit Unit := ⟨⟨fun a _ _ => a = true⟩, fun _ _ => False⟩

theorem HMv_bisim (r : Bool → Bool → Prop) : HMv.lts.IsHomBisimulation r :=
  fun _ _ _ _ => ⟨fun _ h => h.elim, fun _ h => h.elim⟩

-- `Cslib.Logic.Modal.propositions_satisfies_conjunction` idx 10: necessary (empty LTS)
theorem h5 : ¬ drop0% Cslib.Logic.Modal.propositions_satisfies_conjunction 10 := fun h => by
  have := @h Unit Unit Unit () () HM0 (fun _ => Logic.Modal.Proposition.false) (Fintype.ofFinite _) () ()
    (fun s2' => s2'.2.elim)
  obtain ⟨_, h1, _⟩ := Satisfies.hml_dynDiamond_iff_exists.mp this
  exact h1

-- `Cslib.Logic.Modal.propositions_satisfies_conjunction` idx 11: necessary (total LTS, stateMap = ⊥)
theorem h6 : ¬ drop0% Cslib.Logic.Modal.propositions_satisfies_conjunction 11 := fun h => by
  have := @h Unit Unit Unit () () HM1 (fun _ => Logic.Modal.Proposition.false) (Fintype.ofFinite _) () ()
    trivial
  obtain ⟨_, _, h2⟩ := Satisfies.hml_dynDiamond_iff_exists.mp this
  exact Satisfies.finiteAnd_iff_forall.mp h2 _
    (propositions_complete (m := HM1) (s := ()) (μ := ()) (finImage := Fintype.ofFinite _)
      (fun _ => Logic.Modal.Proposition.false) ⟨(), trivial⟩)

def dTop : HML.Proposition Unit Unit :=
  Logic.HasDynamicDiamond.dynDiamond (() : Unit) Logic.Modal.Proposition.true

theorem HMt_true : Satisfies HMt.toModal true dTop :=
  Satisfies.hml_dynDiamond_iff_exists.mpr ⟨true, rfl, Satisfies.true⟩
theorem HMt_false : ¬ Satisfies HMt.toModal false dTop := fun h => by
  obtain ⟨_, h1, _⟩ := Satisfies.hml_dynDiamond_iff_exists.mp h
  exact Bool.false_ne_true h1

-- `Cslib.Logic.Modal.bisimulation_satisfies` idx 7: necessary (total relation, true can move, false cannot)
theorem h7 : ¬ drop0% Cslib.Logic.Modal.bisimulation_satisfies 7 := fun h =>
  HMt_false ((@h Bool Unit Unit HMt (fun _ _ => True) true false (fun _ _ => Iff.rfl) trivial dTop).mp HMt_true)

-- `Cslib.Logic.Modal.bisimulation_satisfies` idx 8: necessary (no transitions, total relation, different atoms)
theorem h8 : ¬ drop0% Cslib.Logic.Modal.bisimulation_satisfies 8 := fun h => by
  have := (@h Bool Unit Unit HMv (fun _ _ => True) true false (HMv_bisim _) trivial (.atom ())).mp rfl
  exact Bool.false_ne_true this

-- `Cslib.Logic.Modal.bisimulation_satisfies` idx 9: necessary (empty relation, different atoms)
theorem h9 : ¬ drop0% Cslib.Logic.Modal.bisimulation_satisfies 9 := fun h => by
  have := (@h Bool Unit Unit HMv (fun _ _ => False) true false (HMv_bisim _) (fun h => h.elim) (.atom ())).mp rfl
  exact Bool.false_ne_true this

-- `Cslib.Logic.Modal.bisimulation_theoryEq` idx 7: necessary (total relation, true can move, false cannot)
theorem h10 : ¬ drop0% Cslib.Logic.Modal.bisimulation_theoryEq 7 := fun h =>
  HMt_false ((Set.ext_iff.mp (@h Bool Unit Unit HMt (fun _ _ => True) true false (fun _ _ => Iff.rfl) trivial) dTop).mp HMt_true)

-- `Cslib.Logic.Modal.bisimulation_theoryEq` idx 8: necessary (no transitions, total relation, different atoms)
theorem h11 : ¬ drop0% Cslib.Logic.Modal.bisimulation_theoryEq 8 := fun h => by
  have := (Set.ext_iff.mp (@h Bool Unit Unit HMv (fun _ _ => True) true false (HMv_bisim _) trivial) (.atom ())).mp rfl
  exact Bool.false_ne_true this

-- `Cslib.Logic.Modal.bisimulation_theoryEq` idx 9: necessary (empty relation, different atoms)
theorem h12 : ¬ drop0% Cslib.Logic.Modal.bisimulation_theoryEq 9 := fun h => by
  have := (Set.ext_iff.mp (@h Bool Unit Unit HMv (fun _ _ => False) true false (HMv_bisim _) (fun h => h.elim)) (.atom ())).mp rfl
  exact Bool.false_ne_true this

-- `Cslib.Logic.Modal.theoryEq_eq_bisimilarity` idx 5: necessary (no transitions: all states bisimilar, atoms differ)
theorem h13 : ¬ drop0% Cslib.Logic.Modal.theoryEq_eq_bisimilarity 5 := fun h => by
  have e := congrFun (congrFun (@h Bool Unit Unit HMv (fun _ _ => inferInstance)) true) false
  have hb : LTS.HomBisimilarity HMv.lts true false := ⟨fun _ _ => True, trivial, HMv_bisim _⟩
  rw [← e] at hb
  have := (Set.ext_iff.mp hb (.atom ())).mp rfl
  exact Bool.false_ne_true this

end W1c5

namespace W1c5
open Cslib Logic.CLL

/-- classical (Boolean) reading of CLL propositions (from Probe2Hand) -/
def bv : Proposition Unit → Prop
  | .atom _ => True
  | .atomDual _ => False
  | .one => True
  | .zero => False
  | .top => True
  | .bot => False
  | .tensor a b => bv a ∧ bv b
  | .parr a b => bv a ∨ bv b
  | .oplus a b => bv a ∨ bv b
  | .with a b => bv a ∧ bv b
  | .bang a => bv a
  | .quest a => bv a

theorem bv_dual (a : Proposition Unit) : bv a.dual ↔ ¬ bv a := by
  induction a <;> simp_all [bv, Proposition.dual] <;> tauto

theorem bv_sound {Γ : Sequent Unit} (p : Proof Γ) : ∃ a ∈ Γ, bv a := by
  induction p with
  | @ax a =>
    by_cases h : bv a
    · exact ⟨a, by simp, h⟩
    · exact ⟨a.dual, by simp, (bv_dual _).mpr h⟩
  | cut p q ihp ihq =>
    obtain ⟨b, hb, hbv⟩ := ihp
    obtain ⟨c, hc, hcv⟩ := ihq
    rw [Multiset.mem_cons] at hb hc
    rcases hb with rfl | hb
    · rcases hc with rfl | hc
      · exact absurd hbv ((bv_dual _).mp hcv)
      · exact ⟨c, Multiset.mem_add.mpr (.inr hc), hcv⟩
    · exact ⟨b, Multiset.mem_add.mpr (.inl hb), hbv⟩
  | one => exact ⟨_, Multiset.mem_cons_self _ _, trivial⟩
  | bot p ih => obtain ⟨b, hb, h⟩ := ih; exact ⟨b, Multiset.mem_cons_of_mem hb, h⟩
  | parr p ih =>
    obtain ⟨b, hb, h⟩ := ih
    simp only [Multiset.mem_cons] at hb
    rcases hb with rfl | rfl | hb
    · exact ⟨_, Multiset.mem_cons_self _ _, Or.inl h⟩
    · exact ⟨_, Multiset.mem_cons_self _ _, Or.inr h⟩
    · exact ⟨b, Multiset.mem_cons_of_mem hb, h⟩
  | tensor p q ihp ihq =>
    obtain ⟨b, hb, hbv⟩ := ihp
    obtain ⟨c, hc, hcv⟩ := ihq
    rw [Multiset.mem_cons] at hb hc
    rcases hb with rfl | hb
    · rcases hc with rfl | hc
      · exact ⟨_, Multiset.mem_cons_self _ _, And.intro hbv hcv⟩
      · exact ⟨c, by simp [hc], hcv⟩
    · exact ⟨b, by simp [hb], hbv⟩
  | oplus₁ p ih =>
    obtain ⟨b, hb, h⟩ := ih
    rw [Multiset.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨_, Multiset.mem_cons_self _ _, Or.inl h⟩
    · exact ⟨b, Multiset.mem_cons_of_mem hb, h⟩
  | oplus₂ p ih =>
    obtain ⟨b, hb, h⟩ := ih
    rw [Multiset.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨_, Multiset.mem_cons_self _ _, Or.inr h⟩
    · exact ⟨b, Multiset.mem_cons_of_mem hb, h⟩
  | «with» p q ihp ihq =>
    obtain ⟨b, hb, hbv⟩ := ihp
    obtain ⟨c, hc, hcv⟩ := ihq
    rw [Multiset.mem_cons] at hb hc
    rcases hb with rfl | hb
    · rcases hc with rfl | hc
      · exact ⟨_, Multiset.mem_cons_self _ _, And.intro hbv hcv⟩
      · exact ⟨c, Multiset.mem_cons_of_mem hc, hcv⟩
    · exact ⟨b, Multiset.mem_cons_of_mem hb, hbv⟩
  | top => exact ⟨_, Multiset.mem_cons_self _ _, trivial⟩
  | quest p ih =>
    obtain ⟨b, hb, h⟩ := ih
    rw [Multiset.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨_, Multiset.mem_cons_self _ _, h⟩
    · exact ⟨b, Multiset.mem_cons_of_mem hb, h⟩
  | weaken p ih => obtain ⟨b, hb, h⟩ := ih; exact ⟨b, Multiset.mem_cons_of_mem hb, h⟩
  | contract p ih =>
    obtain ⟨b, hb, h⟩ := ih
    simp only [Multiset.mem_cons] at hb
    rcases hb with rfl | rfl | hb
    · exact ⟨_, Multiset.mem_cons_self _ _, h⟩
    · exact ⟨_, Multiset.mem_cons_self _ _, h⟩
    · exact ⟨b, Multiset.mem_cons_of_mem hb, h⟩
  | bang _ p ih =>
    obtain ⟨b, hb, h⟩ := ih
    rw [Multiset.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨_, Multiset.mem_cons_self _ _, h⟩
    · exact ⟨b, Multiset.mem_cons_of_mem hb, h⟩

/-- equivalent propositions have the same classical truth value -/
theorem bv_equiv {a b : Proposition Unit} (h : Proposition.Equiv a b) : bv a → bv b := by
  intro ha
  obtain ⟨⟨p⟩, _⟩ := h
  obtain ⟨c, hc, hcv⟩ := bv_sound p
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hc
  rcases hc with rfl | rfl
  · exact absurd ha ((bv_dual _).mp hcv)
  · exact hcv

-- `Cslib.Logic.CLL.Proposition.Equiv.symm` idx 3: necessary (a = 0, b = 1)
theorem c1 : ¬ drop0% Cslib.Logic.CLL.Proposition.Equiv.symm 3 := fun h =>
  bv_equiv (@h Unit .zero .one) trivial

-- `Cslib.Logic.CLL.Proposition.Equiv.trans` idx 4: necessary (a = 1, b = c = 0)
theorem c2 : ¬ drop0% Cslib.Logic.CLL.Proposition.Equiv.trans 4 := fun h =>
  bv_equiv (@h Unit .one .zero .zero (Proposition.Equiv.refl _)) trivial

-- `Cslib.Logic.CLL.Proposition.Equiv.trans` idx 5: necessary (a = b = 1, c = 0)
theorem c3 : ¬ drop0% Cslib.Logic.CLL.Proposition.Equiv.trans 5 := fun h =>
  bv_equiv (@h Unit .one .one .zero (Proposition.Equiv.refl _)) trivial

-- `Cslib.Logic.CLL.Proposition.Equiv.dual` idx 3: necessary (a = ⊥, b = ⊤)
theorem c4 : ¬ drop0% Cslib.Logic.CLL.Proposition.Equiv.dual 3 := fun h =>
  bv_equiv (@h Unit .bot .top) (by simp [bv, Proposition.dual])

-- `Cslib.Logic.CLL.Proposition.Proposition.equiv_tensor₁` idx 4: necessary (a = 1, a' = 0, b = 1)
theorem c5 : ¬ drop0% _private.Cslib.Logics.LinearLogic.CLL.Basic.«0».Cslib.Logic.CLL.Proposition.Proposition.equiv_tensor₁ 4 := fun h =>
  absurd (bv_equiv (@h Unit .one .zero .one) ⟨trivial, trivial⟩) (by simp [bv])

-- `Cslib.Logic.CLL.Proposition.Proposition.equiv_tensor₂` idx 4: necessary (a = 1, b = 1, b' = 0)
theorem c6 : ¬ drop0% _private.Cslib.Logics.LinearLogic.CLL.Basic.«0».Cslib.Logic.CLL.Proposition.Proposition.equiv_tensor₂ 4 := fun h =>
  absurd (bv_equiv (@h Unit .one .one .zero) ⟨trivial, trivial⟩) (by simp [bv])

-- `Cslib.Logic.CLL.Proposition.Proposition.equiv_parr₁` idx 4: necessary (a = 1, a' = 0, b = 0)
theorem c7 : ¬ drop0% _private.Cslib.Logics.LinearLogic.CLL.Basic.«0».Cslib.Logic.CLL.Proposition.Proposition.equiv_parr₁ 4 := fun h =>
  absurd (bv_equiv (@h Unit .one .zero .zero) (Or.inl trivial)) (by simp [bv])

-- `Cslib.Logic.CLL.Proposition.Proposition.equiv_parr₂` idx 4: necessary (a = 0, b = 1, b' = 0)
theorem c8 : ¬ drop0% _private.Cslib.Logics.LinearLogic.CLL.Basic.«0».Cslib.Logic.CLL.Proposition.Proposition.equiv_parr₂ 4 := fun h =>
  absurd (bv_equiv (@h Unit .zero .one .zero) (Or.inr trivial)) (by simp [bv])

-- `Cslib.Logic.CLL.Proposition.Proposition.equiv_oplus₁` idx 4: necessary (a = 1, a' = 0, b = 0)
theorem c9 : ¬ drop0% _private.Cslib.Logics.LinearLogic.CLL.Basic.«0».Cslib.Logic.CLL.Proposition.Proposition.equiv_oplus₁ 4 := fun h =>
  absurd (bv_equiv (@h Unit .one .zero .zero) (Or.inl trivial)) (by simp [bv])

-- `Cslib.Logic.CLL.Proposition.Proposition.equiv_oplus₂` idx 4: necessary (a = 0, b = 1, b' = 0)
theorem c10 : ¬ drop0% _private.Cslib.Logics.LinearLogic.CLL.Basic.«0».Cslib.Logic.CLL.Proposition.Proposition.equiv_oplus₂ 4 := fun h =>
  absurd (bv_equiv (@h Unit .zero .one .zero) (Or.inr trivial)) (by simp [bv])

-- `Cslib.Logic.CLL.Proposition.Proposition.equiv_with₁` idx 4: necessary (a = 1, a' = 0, b = 1)
theorem c11 : ¬ drop0% _private.Cslib.Logics.LinearLogic.CLL.Basic.«0».Cslib.Logic.CLL.Proposition.Proposition.equiv_with₁ 4 := fun h =>
  absurd (bv_equiv (@h Unit .one .zero .one) ⟨trivial, trivial⟩) (by simp [bv])

-- `Cslib.Logic.CLL.Proposition.Proposition.equiv_with₂` idx 4: necessary (a = 1, b = 1, b' = 0)
theorem c12 : ¬ drop0% _private.Cslib.Logics.LinearLogic.CLL.Basic.«0».Cslib.Logic.CLL.Proposition.Proposition.equiv_with₂ 4 := fun h =>
  absurd (bv_equiv (@h Unit .one .one .zero) ⟨trivial, trivial⟩) (by simp [bv])

-- `Cslib.Logic.CLL.Proposition.Proposition.equiv_quest` idx 3: necessary (a = 1, a' = 0)
theorem c13 : ¬ drop0% _private.Cslib.Logics.LinearLogic.CLL.Basic.«0».Cslib.Logic.CLL.Proposition.Proposition.equiv_quest 3 := fun h =>
  absurd (bv_equiv (@h Unit .one .zero) trivial) (by simp [bv])

-- `Cslib.Logic.CLL.Proof.onlyAtomicAxioms_rwConclusion` idx 3: necessary (p = axiom on an atom, Δ = 0)
theorem c14 : ¬ indep0% Cslib.Logic.CLL.Proof.onlyAtomicAxioms_rwConclusion 3 := fun h => by
  have := @h Unit _ 0 (Proof.ax (a := Proposition.atom ())) rfl
  simp at this

-- `Cslib.Logic.CLL.Proof.onlyAtomicAxioms_rwConclusion` idx 5: necessary (axiom on 1, heq = rfl)
theorem c15 : ¬ drop0% Cslib.Logic.CLL.Proof.onlyAtomicAxioms_rwConclusion 5 := fun h => by
  have := @h Unit _ _ rfl (Proof.ax (a := Proposition.one))
  revert this; decide

universe u
-- `Cslib.Logic.CLL.Proof.expand_onlyAtomicAxioms_dual` idx 2: removable (instance of the public Proof.expand_onlyAtomicAxioms at a⫠)
theorem c16 : drop% _private.Cslib.Logics.LinearLogic.CLL.EtaExpansion.«0».Cslib.Logic.CLL.Proof.expand_onlyAtomicAxioms_dual 2 :=
  fun {Atom} {a} => Proof.expand_onlyAtomicAxioms (Atom := Atom) a.dual

-- `Cslib.Logic.CLL.Proposition.isMLL_dual` idx 2: necessary (a = 0, dual ⊤)
theorem c17 : ¬ drop0% Cslib.Logic.CLL.Proposition.isMLL_dual 2 := fun h => by
  have := @h Unit .zero
  simp [Proposition.dual] at this

-- `Cslib.Logic.CLL.Proposition.Context.isMLL_fill` idx 3: necessary (c = hole ⊗ 0, a = 1)
theorem c20 : ¬ drop0% Cslib.Logic.CLL.Proposition.Context.isMLL_fill 3 := fun h => by
  have h2 := (@h Unit (.tensorL .hole .zero) .one).mpr trivial
  simp [Proposition.Context.fill] at h2

-- `Cslib.Logic.CLL.Proof.isMLL_sequent` idx 3: necessary (the ⊤ rule)
theorem c18 : ¬ drop0% Cslib.Logic.CLL.Proof.isMLL_sequent 3 := fun h => by
  have := @h Unit _ (Proof.top (Γ := 0))
  have h2 := this _ (Multiset.mem_cons_self _ _)
  cases h2

-- `Cslib.Logic.CLL.Proof.isMLL_cutFree` idx 3: necessary (the ⊤ rule is cut-free, not MLL)
theorem c19 : ¬ drop0% Cslib.Logic.CLL.Proof.isMLL_cutFree 3 := fun h => by
  have := @h Unit _ (Proof.top (Γ := 0)) rfl
  simp [Proof.IsMLL] at this

end W1c5

namespace W1c5
open Cslib Logic.CLL PhaseSpace

def PU := Unit
instance : CommMonoid PU := inferInstanceAs (CommMonoid Unit)
/-- phase space on Unit with ⊥ = ∅ (facts: ∅ and univ) -/
instance : PhaseSpace PU := { bot := ∅ }
def PV := Unit
instance : CommMonoid PV := inferInstanceAs (CommMonoid Unit)
/-- phase space on Unit with ⊥ = univ (every orthogonal is univ; ∅ is not a fact) -/
instance : PhaseSpace PV := { bot := Set.univ }
def PN := ℕ
instance : CommMonoid PN := inferInstanceAs (CommMonoid ℕ)
/-- phase space on (ℕ, *) with ⊥ = {1} (so 1 = {1}) -/
instance : PhaseSpace PN := { bot := {(1 : ℕ)} }

def pu : PU := ()
def pv : PV := ()
def n0 : PN := (0 : ℕ)
def n1 : PN := (1 : ℕ)

theorem orthE : orthogonal (∅ : Set PU) = Set.univ := by
  ext x; simp [orthogonal, imp]
theorem orthU : orthogonal (Set.univ : Set PU) = ∅ := by
  ext x
  simp only [orthogonal, imp, Set.mem_empty_iff_false, iff_false]
  intro hx
  exact hx () trivial
theorem orthV (X : Set PV) : orthogonal X = Set.univ := by
  ext x; simp [orthogonal, imp]; intro _ _; trivial
theorem PV_empty_not_fact : ¬ isFact (∅ : Set PV) := fun h => by
  unfold isFact at h; simp only [orthV] at h
  have : pv ∈ (∅ : Set PV) := h ▸ Set.mem_univ pv
  exact this
theorem PV_univ_fact : isFact (Set.univ : Set PV) := by
  unfold isFact; simp only [orthV]
theorem PU_one_mem : pu ∈ (1 : Fact PU) := mem_one.mpr fun _ hq => hq
theorem PU_zero_not_mem : pu ∉ (0 : Fact PU) := fun h => mem_zero.mp h pu
theorem PN_one_mem : n1 ∈ (1 : Fact PN) := mem_one.mpr fun x hx => by
  cases hx; rfl

-- `Cslib.Logic.CLL.PhaseSpace.orth_antitone` idx 4: necessary (⊥ = ∅ on Unit, X = univ, Y = ∅)
theorem p1 : ¬ drop0% Cslib.Logic.CLL.PhaseSpace.orth_antitone 4 := fun h => by
  have := @h PU _ Set.univ ∅
  rw [orthE, orthU] at this
  exact this (Set.mem_univ pu)

-- `Cslib.Logic.CLL.PhaseSpace.Fact.mkSubset_coe` idx 3: necessary (⊥ = univ on Unit, G = ∅)
theorem p2 : ¬ indep0% Cslib.Logic.CLL.PhaseSpace.Fact.mkSubset_coe 3 := fun h => by
  have := @h PV _ ∅
  simp only [orthV] at this
  exact this (Set.mem_univ pu)

-- `Cslib.Logic.CLL.PhaseSpace.dual_subset_dual` idx 4: necessary (⊥ = ∅ on Unit, G = univ, H = ∅)
theorem p3 : ¬ drop0% Cslib.Logic.CLL.PhaseSpace.dual_subset_dual 4 := fun h => by
  have := @h PU _ Set.univ ∅
  rw [orthE, orthU] at this
  exact this (Set.mem_univ pu)

-- `Cslib.Logic.CLL.PhaseSpace.coe_mk` idx 3: necessary (⊥ = univ on Unit, ∅ is not a fact)
theorem p4 : ¬ indep0% Cslib.Logic.CLL.PhaseSpace.coe_mk 3 := fun h =>
  PV_empty_not_fact (@h PV _ ∅)

-- `Cslib.Logic.CLL.PhaseSpace.mul_mem_one` idx 4: necessary ((ℕ, *), ⊥ = {1}, p = 0, q = 1)
theorem p5 : ¬ drop0% Cslib.Logic.CLL.PhaseSpace.mul_mem_one 4 := fun h => by
  have h3 : (0 : ℕ) * 1 * 1 = 1 := mem_one.mp (@h PN _ n0 n1 PN_one_mem) n1 rfl
  omega

-- `Cslib.Logic.CLL.PhaseSpace.mul_mem_one` idx 5: necessary ((ℕ, *), ⊥ = {1}, p = 1, q = 0)
theorem p6 : ¬ drop0% Cslib.Logic.CLL.PhaseSpace.mul_mem_one 5 := fun h => by
  have h3 : (1 : ℕ) * 0 * 1 = 1 := mem_one.mp (@h PN _ n1 n0 PN_one_mem) n1 rfl
  omega

-- `Cslib.Logic.CLL.PhaseSpace.biorth_least_fact` idx 4: necessary (⊥ = univ on Unit, G = F = ∅)
theorem p7 : ¬ drop0% Cslib.Logic.CLL.PhaseSpace.biorth_least_fact 4 := fun h => by
  have := @h PV _ ∅ ∅ (subset_refl _)
  simp only [orthV] at this
  exact this (Set.mem_univ pu)

-- `Cslib.Logic.CLL.PhaseSpace.zero_least_fact` idx 3: necessary (⊥ = univ on Unit, F = ∅)
theorem p8 : ¬ drop0% Cslib.Logic.CLL.PhaseSpace.zero_least_fact 3 := fun h => by
  have := @h PV _ ∅
  have h0 : pv ∈ (0 : Fact PV) := mem_zero.mpr fun _ => trivial
  exact this h0

-- `Cslib.Logic.CLL.PhaseSpace.inter_isFact_of_isFact` idx 4: necessary (⊥ = univ on Unit, A = ∅, B = univ)
theorem p9 : ¬ drop0% Cslib.Logic.CLL.PhaseSpace.inter_isFact_of_isFact 4 := fun h => by
  have := @h PV _ ∅ Set.univ PV_univ_fact
  rw [Set.empty_inter] at this
  exact PV_empty_not_fact this

-- `Cslib.Logic.CLL.PhaseSpace.inter_isFact_of_isFact` idx 5: necessary (⊥ = univ on Unit, A = univ, B = ∅)
theorem p10 : ¬ drop0% Cslib.Logic.CLL.PhaseSpace.inter_isFact_of_isFact 5 := fun h => by
  have := @h PV _ Set.univ ∅ PV_univ_fact
  rw [Set.inter_empty] at this
  exact PV_empty_not_fact this

-- `Cslib.Logic.CLL.PhaseSpace.Fact.tensor_le_tensor` idx 6: necessary (⊥ = ∅ on Unit, G = H = L = 1, K = 0)
theorem p11 : ¬ drop0% Cslib.Logic.CLL.PhaseSpace.Fact.tensor_le_tensor 6 := fun h => by
  have := @h PU _ 1 0 1 1 le_rfl
  rw [Fact.tensor_one, Fact.tensor_one] at this
  exact PU_zero_not_mem (this PU_one_mem)

-- `Cslib.Logic.CLL.PhaseSpace.Fact.tensor_le_tensor` idx 7: necessary (⊥ = ∅ on Unit, G = K = H = 1, L = 0)
theorem p12 : ¬ drop0% Cslib.Logic.CLL.PhaseSpace.Fact.tensor_le_tensor 7 := fun h => by
  have := @h PU _ 1 1 1 0 le_rfl
  rw [Fact.one_tensor, Fact.one_tensor] at this
  exact PU_zero_not_mem (this PU_one_mem)

-- `Cslib.Logic.CLL.PhaseSpace.Fact.par_le_par` idx 6: necessary (⊥ = ∅ on Unit, G = 1, K = 0, H = L = ⊥)
theorem p13 : ¬ drop0% Cslib.Logic.CLL.PhaseSpace.Fact.par_le_par 6 := fun h => by
  have := @h PU _ 1 ⊥ 0 ⊥ le_rfl
  rw [Fact.par_bot, Fact.par_bot] at this
  exact PU_zero_not_mem (this PU_one_mem)

-- `Cslib.Logic.CLL.PhaseSpace.Fact.par_le_par` idx 7: necessary (⊥ = ∅ on Unit, G = K = ⊥, H = 1, L = 0)
theorem p14 : ¬ drop0% Cslib.Logic.CLL.PhaseSpace.Fact.par_le_par 7 := fun h => by
  have := @h PU _ ⊥ 1 ⊥ 0 le_rfl
  rw [Fact.bot_par, Fact.bot_par] at this
  exact PU_zero_not_mem (this PU_one_mem)

end W1c5

namespace W1c5
open Cslib Logic.Modal


def tt : Logic.Modal.Proposition τU Unit := .true
def ff : Logic.Modal.Proposition τU Unit := .false
def pa : Logic.Modal.Proposition τU Unit := .atom ()
/-- empty / total frames on Unit -/
def F0 : Frame Unit τU := ⟨fun _ _ _ => False⟩
def F1 : Frame Unit τU := ⟨fun _ _ _ => True⟩
def MU0 : Model Unit τU Unit := ⟨F0, fun _ _ => False⟩
def MU1 : Model Unit τU Unit := ⟨F1, fun _ _ => False⟩
/-- single edge false → true -/
def FE : Frame Bool τU := Frame.ofRelation (fun a b => a = false ∧ b = true)
/-- successor frame on ℕ -/
def FS : Frame ℕ τU := Frame.ofRelation (fun a b => b = a + 1)
/-- binary tree on ℕ -/
def FT : Frame ℕ τU := Frame.ofRelation (fun a b => b = 2 * a + 1 ∨ b = 2 * a + 2)
/-- 0 → 1, 0 → 2 -/
def FP : Frame ℕ τU := Frame.ofRelation (fun a b => a = 0 ∧ (b = 1 ∨ b = 2))

/-- in a serial unary frame, atom-free propositions are true at all worlds or at none -/
theorem unif {W : Type} (f : Frame W τU) (hs : ∀ op w, ∃ w', f.r op w (fun _ => w'))
    (v : W → Empty → Prop) (φ : Logic.Modal.Proposition τU Empty) :
    ∀ w w', Satisfies ⟨f, v⟩ w φ ↔ Satisfies ⟨f, v⟩ w' φ := by
  induction φ with
  | atom p => exact p.elim
  | false => intro w w'; exact Iff.rfl
  | not φ ih => intro w w'; exact not_congr (ih w w')
  | or a b iha ihb => intro w w'; exact or_congr (iha w w') (ihb w w')
  | triangle op φs ih =>
    intro w w'
    constructor
    · rintro ⟨ws, _, h⟩
      obtain ⟨u, hu⟩ := hs op w'
      exact ⟨fun _ => u, hu, fun i => (ih i (ws i) u).1 (h i)⟩
    · rintro ⟨ws, _, h⟩
      obtain ⟨u, hu⟩ := hs op w
      exact ⟨fun _ => u, hu, fun i => (ih i (ws i) u).1 (h i)⟩

theorem FSser : ∀ op w, ∃ w', FS.r op w (fun _ => w') := fun _ w => ⟨w + 1, rfl⟩
theorem FTser : ∀ op w, ∃ w', FT.r op w (fun _ => w') := fun _ w => ⟨2 * w + 1, Or.inl rfl⟩

-- `Cslib.Logic.Modal.Proposition.denotation_eq_of_equiv` idx 6: necessary (φ₁ = ⊤, φ₂ = ⊥)
theorem m1 : ¬ drop0% Cslib.Logic.Modal.Proposition.denotation_eq_of_equiv 6 := fun h => by
  have e := h (m := MU0) (φ₁ := tt) (φ₂ := ff)
  have h1 : () ∈ Proposition.denotation MU0 tt := satisfies_mem_denotation.mpr Satisfies.true
  rw [e] at h1
  exact satisfies_mem_denotation.mp h1

-- `Cslib.Logic.Modal.Proposition.ofContainers_inf_equiv` idx 8: necessary (Bool containers, b ∋ x iff b, p ⊓ q := true, p = q = false)
theorem m2 : ¬ drop0% Cslib.Logic.Modal.Proposition.ofContainers_inf_equiv 8 := fun h => by
  have := @h Unit Bool τU ⟨fun b _ => b = true⟩ ⟨fun _ _ => true⟩ F1 false false
  have h2 := (Proposition.equiv_iff_forall_iff.mp this ()).mp rfl
  exact Bool.false_ne_true (Satisfies.and_iff_and.mp h2).1

-- `Cslib.Logic.Modal.Proposition.equiv_of_EquivWithin` idx 6: necessary (S = univ, ⊤ vs ⊥)
theorem m3 : ¬ drop0% Cslib.Logic.Modal.Proposition.equiv_of_EquivWithin 6 := fun h =>
  (Proposition.equiv_iff_forall_iff.mp (h (φ₁ := tt) (φ₂ := ff) (S := Set.univ) MU0 (Set.mem_univ _)) ()).mp
    Satisfies.true

-- `Cslib.Logic.Modal.Proposition.equiv_of_EquivWithin` idx 8: necessary (S = ∅, ⊤ vs ⊥)
theorem m4 : ¬ drop0% Cslib.Logic.Modal.Proposition.equiv_of_EquivWithin 8 := fun h =>
  (Proposition.equiv_iff_forall_iff.mp (h (φ₁ := tt) (φ₂ := ff) (S := ∅) (fun _ hm => hm.elim) MU0) ()).mp
    Satisfies.true

-- `Cslib.Logic.Modal.Proposition.equivWithin_valid` idx 6: necessary (S = univ, ⊤ vs ⊥)
theorem m5 : ¬ drop0% Cslib.Logic.Modal.Proposition.equivWithin_valid 6 := fun h =>
  (@h Unit τU Unit Set.univ tt ff).mp (fun _ _ _ => Satisfies.true) MU0 trivial ()

-- `Cslib.Logic.Modal.Proposition.equiv_of_axiom` idx 6: necessary (⊤ vs ⊥)
theorem m6 : ¬ drop0% Cslib.Logic.Modal.Proposition.equiv_of_axiom 6 := fun h =>
  (Proposition.equiv_iff_forall_iff.mp (h (f := F0) (φ₁ := tt) (φ₂ := ff) (fun _ _ => False)) ()).mp
    Satisfies.true

-- `Cslib.Logic.Modal.satisfies_theory` idx 6: necessary (φ = ⊥)
theorem m7 : ¬ drop0% Cslib.Logic.Modal.satisfies_theory 6 := fun h =>
  (h (m := MU0) (w := ()) (φ := ff) : Satisfies MU0 () ff)

-- `Cslib.Logic.Modal.not_theoryEq_satisfies` idx 6: necessary (w₁ = w₂)
theorem m8 : ¬ drop0% Cslib.Logic.Modal.not_theoryEq_satisfies 6 := fun h => by
  obtain ⟨_, h1, h2⟩ := h (m := MU0) (w₁ := ()) (w₂ := ())
  exact h2 h1

/-- two worlds, atom true exactly at true -/
def MB : Model Bool τU Unit := ⟨FE, fun w _ => w = true⟩

-- `Cslib.Logic.Modal.theoryEq_satisfies` idx 7: necessary (atom true at w₁ only)
theorem m9 : ¬ drop0% Cslib.Logic.Modal.theoryEq_satisfies 7 := fun h =>
  Bool.false_ne_true (h (m := MB) (w₁ := true) (w₂ := false) (φ := pa) rfl)

-- `Cslib.Logic.Modal.Satisfies.der_of_axiom` idx 6: necessary (φ = ⊥)
theorem m10 : ¬ drop0% Cslib.Logic.Modal.Satisfies.der_of_axiom 6 := fun h =>
  (h (m := MU0) (w := ()) (φ := ff) : Satisfies MU0 () ff)

-- `Cslib.Logic.Modal.Satisfies.of_axiom` idx 5: necessary (φ = ⊥)
theorem m11 : ¬ drop0% Cslib.Logic.Modal.Satisfies.of_axiom 5 := fun h =>
  (h MU0 ff () : Satisfies MU0 () ff)

-- `Cslib.Logic.Modal.Satisfies.k` idx 10: necessary (total frame, φs = ⊤, φ₁ = ⊤, φ₂ = ⊥)
theorem m12 : ¬ drop0% Cslib.Logic.Modal.Satisfies.k 10 := fun h => by
  have h1 := (Satisfies.axiom_def _).mpr (h (f := F1) (op := ()) (φs := fun _ => tt) (i := ()) (φ₁ := tt) (φ₂ := ff))
    (fun _ _ => False) ()
  rw [Satisfies.imp_iff_imp, Satisfies.imp_iff_imp] at h1
  have h3 := h1 (Satisfies.nabla_iff_forall.mpr fun _ _ => ⟨(), Satisfies.true⟩)
    (Satisfies.nabla_iff_forall.mpr fun _ _ => ⟨(), Satisfies.subst_apply_iff.mpr (Or.inl ⟨rfl, Satisfies.true⟩)⟩)
  obtain ⟨i, hi⟩ := Satisfies.nabla_iff_forall.mp h3 (fun _ => ()) trivial
  rcases Satisfies.subst_apply_iff.mp hi with ⟨_, h4⟩ | ⟨h4, _⟩
  · exact h4
  · exact h4 rfl

-- `Cslib.Logic.Modal.Satisfies.triangle_and_nabla` idx 9: necessary (empty frame)
theorem m13 : ¬ drop0% Cslib.Logic.Modal.Satisfies.triangle_and_nabla 9 := fun h => by
  obtain ⟨_, hi⟩ := h (m := MU0) (w := ()) (op := ()) (φs₁ := fun _ => tt) (φs₂ := fun _ => tt)
  obtain ⟨_, hr, _⟩ := Satisfies.triangle_iff_exists.mp hi
  exact hr

-- `Cslib.Logic.Modal.Satisfies.triangle_of_nabla` idx 9: necessary (empty frame)
theorem m14 : ¬ drop0% Cslib.Logic.Modal.Satisfies.triangle_of_nabla 9 := fun h => by
  obtain ⟨_, hi⟩ := h (m := MU0) (w := ()) (op := ()) (φs₁ := fun _ => tt) (φs₂ := fun _ => tt)
  obtain ⟨_, hr, _⟩ := Satisfies.triangle_iff_exists.mp hi
  exact hr

-- `Cslib.Logic.Modal.Satisfies.triangle_of_diagonal` idx 7: necessary (empty frame, φ = ⊤)
theorem m15 : ¬ drop0% Cslib.Logic.Modal.Satisfies.triangle_of_diagonal 7 := fun h => by
  obtain ⟨_, hr, _⟩ := Satisfies.triangle_iff_exists.mp
    (h (m := MU0) (op := ()) (w := ()) (φ := tt) Satisfies.true)
  exact hr

-- `Cslib.Logic.Modal.Satisfies.triangle_of_diagonal` idx 8: necessary (total frame, φ = ⊥)
theorem m16 : ¬ drop0% Cslib.Logic.Modal.Satisfies.triangle_of_diagonal 8 := fun h => by
  obtain ⟨_, _, hs⟩ := Satisfies.triangle_iff_exists.mp
    (h (m := MU1) (op := ()) (w := ()) (φ := ff) (instRefl := ⟨fun _ => trivial⟩))
  exact hs ()

-- `Cslib.Logic.Modal.Satisfies.t` idx 5: necessary (empty frame, φ = ⊤)
theorem m17 : ¬ drop0% Cslib.Logic.Modal.Satisfies.t 5 := fun h => by
  have h1 := (Satisfies.axiom_def _).mpr (h (op := ()) F0 tt) (fun _ _ => False) ()
  obtain ⟨_, hr, _⟩ := Satisfies.triangle_iff_exists.mp (Satisfies.imp_iff_imp.mp h1 Satisfies.true)
  exact hr

-- `Cslib.Logic.Modal.Satisfies.t_nabla_triangle` idx 6: necessary (empty frame, φ = ⊤)
theorem m18 : ¬ drop0% Cslib.Logic.Modal.Satisfies.t_nabla_triangle 6 := fun h => by
  have h1 := (Satisfies.axiom_def _).mpr (h (op := ()) (φ := tt) F0) (fun _ _ => False) ()
  have h2 := Satisfies.iff_iff_iff.mp h1 |>.mp (Satisfies.imp_iff_imp.mpr fun _ => Satisfies.true)
  obtain ⟨_, hr, _⟩ := Satisfies.triangle_iff_exists.mp (Satisfies.imp_iff_imp.mp h2 Satisfies.true)
  exact hr

-- `Cslib.Logic.Modal.Satisfies.b` idx 5: necessary (single edge false → true, φ = ⊤)
theorem m19 : ¬ drop0% Cslib.Logic.Modal.Satisfies.b 5 := fun h => by
  have h1 := (Satisfies.axiom_def _).mpr (h (op := ()) FE tt) (fun _ _ => False) false
  obtain ⟨_, h2⟩ := Satisfies.nabla_iff_forall.mp (Satisfies.imp_iff_imp.mp h1 Satisfies.true)
    (fun _ => true) ⟨rfl, rfl⟩
  obtain ⟨_, hr, _⟩ := Satisfies.triangle_iff_exists.mp h2
  exact Bool.noConfusion hr.1

/-- atom true only at 2 -/
def MS2 : Model ℕ τU Unit := ⟨FS, fun n _ => n = 2⟩

-- `Cslib.Logic.Modal.Satisfies.four` idx 5: necessary (successor frame 0 → 1 → 2, atom at 2)
theorem m20 : ¬ drop0% Cslib.Logic.Modal.Satisfies.four 5 := fun h => by
  have h1 := (Satisfies.axiom_def _).mpr (h (op := ()) FS (fun _ => Logic.HasTriangle.triangle () (fun _ => pa))
    (fun _ => pa) () rfl) (fun n _ => n = 2) 0
  obtain ⟨ws, hr, hs⟩ := Satisfies.triangle_iff_exists.mp (Satisfies.imp_iff_imp.mp h1
    (Satisfies.triangle_iff_exists.mpr ⟨fun _ => 1, rfl, fun _ =>
      Satisfies.triangle_iff_exists.mpr ⟨fun _ => 2, rfl, fun _ => rfl⟩⟩))
  have e1 : ws () = 0 + 1 := hr
  have e2 : ws () = 2 := hs ()
  omega

-- `Cslib.Logic.Modal.Satisfies.four` idx 9: necessary (total frame, φs = ⊤, ψs = ⊥)
theorem m21 : ¬ drop0% Cslib.Logic.Modal.Satisfies.four 9 := fun h => by
  have h1 := (Satisfies.axiom_def _).mpr (@h Unit τU () Unit F1 ⟨fun _ _ _ _ _ _ => trivial⟩
    (fun _ => tt) (fun _ => ff) ()) (fun _ _ => False) ()
  obtain ⟨_, _, hs⟩ := Satisfies.triangle_iff_exists.mp (Satisfies.imp_iff_imp.mp h1
    (Satisfies.triangle_iff_exists.mpr ⟨fun _ => (), trivial, fun _ => Satisfies.true⟩))
  exact hs ()

-- `Cslib.Logic.Modal.Satisfies.five` idx 5: necessary (single edge false → true, φs = ⊤)
theorem m22 : ¬ drop0% Cslib.Logic.Modal.Satisfies.five 5 := fun h => by
  have h1 := (Satisfies.axiom_def _).mpr (h (op := ()) FE (fun _ => tt)) (fun _ _ => False) false
  have h2 := Satisfies.imp_iff_imp.mp h1
    (Satisfies.triangle_iff_exists.mpr ⟨fun _ => true, ⟨rfl, rfl⟩, fun _ => Satisfies.true⟩)
  obtain ⟨_, h3⟩ := Satisfies.nabla_iff_forall.mp h2 (fun _ => true) ⟨rfl, rfl⟩
  obtain ⟨_, hr, _⟩ := Satisfies.triangle_iff_exists.mp h3
  exact Bool.noConfusion hr.1

-- `Cslib.Logic.Modal.Satisfies.t_refl` idx 5: necessary (Atom = Empty; successor frame: atom-free T holds, not reflexive)
theorem m23 : ¬ drop0% Cslib.Logic.Modal.Satisfies.t_refl 5 := fun h => by
  have := (h (World := ℕ) (τ := τU) (Atom := Empty) FS (op := ()) (fun φ => (Satisfies.axiom_def _).mp
    fun v w => Satisfies.imp_iff_imp.mpr fun hw => Satisfies.triangle_iff_exists.mpr
      ⟨fun _ => w + 1, rfl, fun _ => (unif FS FSser v φ w (w + 1)).1 hw⟩)).refl 0
  change 0 = 0 + 1 at this
  omega

-- `Cslib.Logic.Modal.Satisfies.t_refl` idx 6: necessary (empty frame)
theorem m24 : ¬ drop0% Cslib.Logic.Modal.Satisfies.t_refl 6 := fun h =>
  (h (World := Unit) (Atom := Unit) F0 (op := ())).refl ()

-- `Cslib.Logic.Modal.Satisfies.b_symm` idx 5: necessary (Atom = Empty; successor frame: atom-free B holds, not symmetric)
theorem m25 : ¬ drop0% Cslib.Logic.Modal.Satisfies.b_symm 5 := fun h => by
  have := (h (World := ℕ) (τ := τU) (Atom := Empty) FS (op := ()) (fun φ => (Satisfies.axiom_def _).mp
    fun v w => Satisfies.imp_iff_imp.mpr fun hw => Satisfies.nabla_iff_forall.mpr fun ws _ =>
      ⟨(), Satisfies.triangle_iff_exists.mpr
        ⟨fun _ => ws () + 1, rfl, fun _ => (unif FS FSser v φ w (ws () + 1)).1 hw⟩⟩)).symm 0 (fun _ => 1) rfl
  obtain ⟨_, hi⟩ := this
  change 0 = 1 + 1 at hi
  omega

-- `Cslib.Logic.Modal.Satisfies.b_symm` idx 6: necessary (single edge false → true)
theorem m26 : ¬ drop0% Cslib.Logic.Modal.Satisfies.b_symm 6 := fun h => by
  obtain ⟨_, hi⟩ := (h (World := Bool) (Atom := Unit) FE (op := ())).symm false (fun _ => true) ⟨rfl, rfl⟩
  exact Bool.noConfusion hi.1

-- `Cslib.Logic.Modal.Satisfies.four_trans` idx 7: necessary (successor frame 0 → 1 → 2)
theorem m27 : ¬ drop0% Cslib.Logic.Modal.Satisfies.four_trans 7 := fun h => by
  have := (h (World := ℕ) (Atom := Unit) FS (op := ()) (Function.Embedding.refl Unit)).trans 0 (fun _ => 1) ()
    (fun _ => 2) rfl rfl
  change 2 = 0 + 1 at this
  omega

-- `Cslib.Logic.Modal.Satisfies.five_rightEuclidean` idx 6: necessary (single edge false → true)
theorem m28 : ¬ drop0% Cslib.Logic.Modal.Satisfies.five_rightEuclidean 6 := fun h => by
  obtain ⟨_, hi⟩ := (h (World := Bool) (Atom := Unit) FE (op := ()) (Function.Embedding.refl Unit)).rightEuclidean
    false (fun _ => true) (fun _ => true) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
  exact Bool.noConfusion hi.1

universe u1 u2 u3 u4
-- `Cslib.Logic.Modal.Satisfies.four_trans` idx 5: removable (without atoms the embedding e forces τ.B op empty, and then Trans holds vacuously)
theorem m29 : drop% Cslib.Logic.Modal.Satisfies.four_trans 5 := by
  intro World τ Atom op f e h
  by_cases hA : Nonempty Atom
  · exact Satisfies.four_trans f e h
  · exact ⟨fun _ _ i _ _ _ => absurd ⟨e i⟩ hA⟩

-- `Cslib.Logic.Modal.Satisfies.dynBox_dynDiamond_diagonalInverse₂` idx 8: necessary (op₂ total, op₁ empty, φ = ⊤)
theorem m30 : ¬ drop0% Cslib.Logic.Modal.Satisfies.dynBox_dynDiamond_diagonalInverse₂ 8 := fun h => by
  have := @h τB _ Unit Unit () ⟨⟨fun op _ _ => op = true⟩, fun _ _ => False⟩ false true Logic.Modal.Proposition.true
  have h1 := Logic.Modal.Satisfies.imp_iff_imp.mp this Logic.Modal.Satisfies.true
  have h2 := Logic.Modal.Satisfies.dynBox_iff_forall.mp h1 () rfl
  obtain ⟨w', hw', _⟩ := Logic.Modal.Satisfies.dynDiamond_iff_exists.mp h2
  exact absurd hw' (by simp [Frame.diagonal])


-- `Cslib.Frame.instReflRelOfRelation` idx 5: necessary (empty relation)
theorem u1 : ¬ drop0% Cslib.Frame.instReflRelOfRelation 5 := fun h =>
  (h (τ := τU) (r := fun (_ _ : Unit) => False)).refl ()

-- `Cslib.Frame.instSymmRelOfRelation` idx 5: necessary (single edge false → true)
theorem u2 : ¬ drop0% Cslib.Frame.instSymmRelOfRelation 5 := fun h =>
  Bool.noConfusion ((h (τ := τU) (r := fun a b : Bool => a = false ∧ b = true)).symm false true ⟨rfl, rfl⟩).1

-- `Cslib.Frame.instIsTransRelOfRelation` idx 5: necessary (successor relation)
theorem u3 : ¬ drop0% Cslib.Frame.instIsTransRelOfRelation 5 := fun h => by
  have := (h (τ := τU) (r := fun a b : ℕ => b = a + 1)).trans 0 1 2 rfl rfl
  change 2 = 0 + 1 at this
  omega

-- `Cslib.Frame.ofRelation_rel_of` idx 7: necessary (empty relation)
theorem u4 : ¬ drop0% Cslib.Frame.ofRelation_rel_of 7 := fun h =>
  (h (τ := τU) (r := fun (_ _ : Unit) => False) (w := ()) (w' := ()) : False)

-- `Cslib.Logic.Modal.Satisfies.diamond_of` idx 9: necessary (empty frame, φ = ⊤)
theorem u5 : ¬ drop0% Cslib.Logic.Modal.Satisfies.diamond_of 9 := fun h => by
  obtain ⟨_, hr, _⟩ := Satisfies.diamond_iff_exists.mp
    (h (τ := τU) (m := MU0) (w := ()) (w' := ()) (φ := tt) Satisfies.true)
  exact hr

-- `Cslib.Logic.Modal.Satisfies.diamond_of` idx 10: necessary (total frame, φ = ⊥)
theorem u6 : ¬ drop0% Cslib.Logic.Modal.Satisfies.diamond_of 10 := fun h => by
  obtain ⟨_, _, hs⟩ := Satisfies.diamond_iff_exists.mp
    (h (τ := τU) (m := MU1) (w := ()) (w' := ()) (φ := ff) trivial)
  exact hs

-- `Cslib.Logic.Modal.Satisfies.unimodal_t` idx 6: necessary (empty frame, φ = ⊤)
theorem u7 : ¬ drop0% Cslib.Logic.Modal.Satisfies.unimodal_t 6 := fun h => by
  have h1 := (Satisfies.axiom_def _).mpr (h (τ := τU) F0 tt) (fun _ _ => False) ()
  obtain ⟨_, hr, _⟩ := Satisfies.diamond_iff_exists.mp (Satisfies.imp_iff_imp.mp h1 Satisfies.true)
  exact hr

-- `Cslib.Logic.Modal.Satisfies.t_box_diamond` idx 8: necessary (empty frame, φ = ⊤)
theorem u8 : ¬ drop0% Cslib.Logic.Modal.Satisfies.t_box_diamond 8 := fun h => by
  have h1 := (h (τ := τU) (m := MU0) (w := ()) (φ := tt)).mp (Satisfies.imp_iff_imp.mpr fun _ => Satisfies.true)
  obtain ⟨_, hr, _⟩ := Satisfies.diamond_iff_exists.mp (Satisfies.imp_iff_imp.mp h1 Satisfies.true)
  exact hr

-- `Cslib.Logic.Modal.Satisfies.unimodal_b` idx 6: necessary (single edge false → true, φ = ⊤)
theorem u9 : ¬ drop0% Cslib.Logic.Modal.Satisfies.unimodal_b 6 := fun h => by
  have h1 := (Satisfies.axiom_def _).mpr (h (τ := τU) FE tt) (fun _ _ => False) false
  have h2 := Satisfies.box_iff_forall.mp (Satisfies.imp_iff_imp.mp h1 Satisfies.true) true ⟨rfl, rfl⟩
  obtain ⟨_, hr, _⟩ := Satisfies.diamond_iff_exists.mp h2
  exact Bool.noConfusion hr.1

-- `Cslib.Logic.Modal.Satisfies.unimodal_four` idx 6: necessary (successor frame 0 → 1 → 2, atom at 2)
theorem u10 : ¬ drop0% Cslib.Logic.Modal.Satisfies.unimodal_four 6 := fun h => by
  have h1 := (Satisfies.axiom_def _).mpr (h (τ := τU) FS pa) (fun n _ => n = 2) 0
  obtain ⟨w, hr, hs⟩ := Satisfies.diamond_iff_exists.mp (Satisfies.imp_iff_imp.mp h1
    (Satisfies.diamond_iff_exists.mpr ⟨1, rfl, Satisfies.diamond_iff_exists.mpr ⟨2, rfl, rfl⟩⟩))
  change w = 0 + 1 at hr
  change w = 2 at hs
  omega

-- `Cslib.Logic.Modal.Satisfies.unimodal_five` idx 6: necessary (single edge false → true, φ = ⊤)
theorem u11 : ¬ drop0% Cslib.Logic.Modal.Satisfies.unimodal_five 6 := fun h => by
  have h1 := (Satisfies.axiom_def _).mpr (h (τ := τU) FE tt) (fun _ _ => False) false
  have h2 := Satisfies.box_iff_forall.mp (Satisfies.imp_iff_imp.mp h1
    (Satisfies.diamond_iff_exists.mpr ⟨true, ⟨rfl, rfl⟩, Satisfies.true⟩)) true ⟨rfl, rfl⟩
  obtain ⟨_, hr, _⟩ := Satisfies.diamond_iff_exists.mp h2
  exact Bool.noConfusion hr.1

-- `Cslib.Logic.Modal.Satisfies.d` idx 6: necessary (empty frame, φ = ⊤)
theorem u12 : ¬ drop0% Cslib.Logic.Modal.Satisfies.d 6 := fun h => by
  have h1 := (Satisfies.axiom_def _).mpr (h (τ := τU) F0 tt) (fun _ _ => False) ()
  obtain ⟨_, hr, _⟩ := Satisfies.diamond_iff_exists.mp (Satisfies.imp_iff_imp.mp h1
    (Satisfies.box_iff_forall.mpr fun _ _ => Satisfies.true))
  exact hr

-- `Cslib.Logic.Modal.Satisfies.unimodal_t_refl` idx 6: necessary (Atom = Empty; successor frame)
theorem u13 : ¬ drop0% Cslib.Logic.Modal.Satisfies.unimodal_t_refl 6 := fun h => by
  have := (h (τ := τU) (Atom := Empty) FS (fun φ => (Satisfies.axiom_def _).mp
    fun v w => Satisfies.imp_iff_imp.mpr fun hw => Satisfies.diamond_iff_exists.mpr
      ⟨w + 1, rfl, (unif FS FSser v φ w (w + 1)).1 hw⟩)).refl 0
  change 0 = 0 + 1 at this
  omega

-- `Cslib.Logic.Modal.Satisfies.unimodal_t_refl` idx 7: necessary (empty frame)
theorem u14 : ¬ drop0% Cslib.Logic.Modal.Satisfies.unimodal_t_refl 7 := fun h =>
  (h (τ := τU) (Atom := Unit) F0).refl ()

-- `Cslib.Logic.Modal.Satisfies.unimodal_b_symm` idx 6: necessary (Atom = Empty; successor frame)
theorem u15 : ¬ drop0% Cslib.Logic.Modal.Satisfies.unimodal_b_symm 6 := fun h => by
  have := (h (τ := τU) (Atom := Empty) FS (fun φ => (Satisfies.axiom_def _).mp
    fun v w => Satisfies.imp_iff_imp.mpr fun hw => Satisfies.box_iff_forall.mpr fun w' _ =>
      Satisfies.diamond_iff_exists.mpr ⟨w' + 1, rfl, (unif FS FSser v φ w (w' + 1)).1 hw⟩)).symm 0 1 rfl
  change 0 = 1 + 1 at this
  omega

-- `Cslib.Logic.Modal.Satisfies.unimodal_b_symm` idx 7: necessary (single edge false → true)
theorem u16 : ¬ drop0% Cslib.Logic.Modal.Satisfies.unimodal_b_symm 7 := fun h =>
  Bool.noConfusion ((h (τ := τU) (Atom := Unit) FE).symm false true ⟨rfl, rfl⟩).1

-- `Cslib.Logic.Modal.Satisfies.unimodal_four_trans` idx 6: necessary (Atom = Empty; successor frame)
theorem u17 : ¬ drop0% Cslib.Logic.Modal.Satisfies.unimodal_four_trans 6 := fun h => by
  have := (h (τ := τU) (Atom := Empty) FS (fun φ => (Satisfies.axiom_def _).mp
    fun v w => Satisfies.imp_iff_imp.mpr fun hw => by
      obtain ⟨w', _, hw'⟩ := Satisfies.diamond_iff_exists.mp hw
      obtain ⟨w'', _, hw''⟩ := Satisfies.diamond_iff_exists.mp hw'
      exact Satisfies.diamond_iff_exists.mpr ⟨w + 1, rfl, (unif FS FSser v φ w'' (w + 1)).1 hw''⟩)).trans 0 1 2 rfl rfl
  change 2 = 0 + 1 at this
  omega

-- `Cslib.Logic.Modal.Satisfies.unimodal_four_trans` idx 7: necessary (successor frame)
theorem u18 : ¬ drop0% Cslib.Logic.Modal.Satisfies.unimodal_four_trans 7 := fun h => by
  have := (h (τ := τU) (Atom := Unit) FS).trans 0 1 2 rfl rfl
  change 2 = 0 + 1 at this
  omega

-- `Cslib.Logic.Modal.Satisfies.unimodal_five_rightEuclidean` idx 6: necessary (Atom = Empty; successor frame)
theorem u19 : ¬ drop0% Cslib.Logic.Modal.Satisfies.unimodal_five_rightEuclidean 6 := fun h => by
  have := (h (τ := τU) (Atom := Empty) FS (fun φ => (Satisfies.axiom_def _).mp
    fun v w => Satisfies.imp_iff_imp.mpr fun hw => by
      obtain ⟨w', _, hw'⟩ := Satisfies.diamond_iff_exists.mp hw
      exact Satisfies.box_iff_forall.mpr fun u _ =>
        Satisfies.diamond_iff_exists.mpr ⟨u + 1, rfl, (unif FS FSser v φ w' (u + 1)).1 hw'⟩)).rightEuclidean
    (a := 0) (b := 1) (c := 1) rfl rfl
  change 1 = 1 + 1 at this
  omega

universe v1 v2 v3 v4
-- `Cslib.Logic.Modal.Satisfies.d_serial` idx 6: removable (instantiate D at ⊤: □⊤ → ◇⊤ yields a successor; no atom needed)
theorem u20 : drop% Cslib.Logic.Modal.Satisfies.d_serial 6 := by
  intro τ _ _ World Atom f h
  refine ⟨fun w => ?_⟩
  have h1 := (Satisfies.axiom_def f).mpr (h Logic.Modal.Proposition.true) (fun _ _ => False) w
  obtain ⟨w', hw', _⟩ := Satisfies.diamond_iff_exists.mp (Satisfies.imp_iff_imp.mp h1
    (Satisfies.box_iff_forall.mpr fun _ _ => Satisfies.true))
  exact ⟨w', hw'⟩

-- `Cslib.Logic.Modal.Satisfies.d_serial` idx 7: necessary (empty frame)
theorem u21 : ¬ drop0% Cslib.Logic.Modal.Satisfies.d_serial 7 := fun h => by
  obtain ⟨_, hb⟩ := (h (τ := τU) (Atom := Unit) F0).serial ()
  exact hb

-- `Cslib.Logic.Modal.Satisfies.pointTwo_diamond` idx 6: necessary (Atom = Empty; binary tree frame: serial, not diamond)
theorem u22 : ¬ drop0% Cslib.Logic.Modal.Satisfies.pointTwo_diamond 6 := fun h => by
  have this : Relation.Diamond FT.rel := (h (τ := τU) (Atom := Empty) FT (fun φ => (Satisfies.axiom_def _).mp
    fun v w => Satisfies.imp_iff_imp.mpr fun hw => by
      obtain ⟨w', _, hw'⟩ := Satisfies.diamond_iff_exists.mp hw
      have hb := Satisfies.box_iff_forall.mp hw' (2 * w' + 1) (Or.inl rfl)
      exact Satisfies.box_iff_forall.mpr fun u _ =>
        Satisfies.diamond_iff_exists.mpr ⟨2 * u + 1, Or.inl rfl, (unif FT FTser v φ _ _).1 hb⟩))
  obtain ⟨d, h1, h2⟩ := @this 0 1 2 (Or.inl rfl) (Or.inr rfl)
  change d = 2 * 1 + 1 ∨ d = 2 * 1 + 2 at h1
  change d = 2 * 2 + 1 ∨ d = 2 * 2 + 2 at h2
  omega

-- `Cslib.Logic.Modal.Satisfies.pointTwo_diamond` idx 7: necessary (0 → 1, 0 → 2, dead ends)
theorem u23 : ¬ drop0% Cslib.Logic.Modal.Satisfies.pointTwo_diamond 7 := fun h => by
  have hd : Relation.Diamond FP.rel := h (τ := τU) (Atom := Unit) FP
  obtain ⟨d, h1, _⟩ := @hd 0 1 2 ⟨rfl, Or.inl rfl⟩ ⟨rfl, Or.inr rfl⟩
  change 1 = 0 ∧ _ at h1
  omega

-- `Cslib.Logic.Modal.Satisfies.pointTwo` idx 6: necessary (0 → 1, 0 → 2, dead ends, φ = ⊥)
theorem u24 : ¬ drop0% Cslib.Logic.Modal.Satisfies.pointTwo 6 := fun h => by
  have h1 := (Satisfies.axiom_def _).mpr (h (τ := τU) FP ff) (fun _ _ => False) 0
  have h2 := Satisfies.imp_iff_imp.mp h1 (Satisfies.diamond_iff_exists.mpr ⟨1, ⟨rfl, Or.inl rfl⟩,
    Satisfies.box_iff_forall.mpr fun w' hw' => absurd (hw'.1 : 1 = 0) (by omega)⟩)
  obtain ⟨_, _, h3⟩ := Satisfies.diamond_iff_exists.mp (Satisfies.box_iff_forall.mp h2 1 ⟨rfl, Or.inl rfl⟩)
  exact h3

/-- 0 → 1 → 2, not transitive, terminating -/
def FL : Frame ℕ τU := Frame.ofRelation (fun a b => b = a + 1 ∧ a < 2)
theorem FL_term : Relation.Terminating FL.rel :=
  Subrelation.wf (fun {a b} (h : a = b + 1 ∧ b < 2) => show 3 - a < 3 - b by omega) (measure fun n : ℕ => 3 - n).wf

-- `Cslib.Logic.Modal.Satisfies.l` idx 6: necessary (0 → 1 → 2 not transitive, φ true only at 0)
theorem u25 : ¬ drop0% Cslib.Logic.Modal.Satisfies.l 6 := fun h => by
  have h1 := (Satisfies.axiom_def _).mpr (h (τ := τU) FL FL_term pa) (fun n _ => n = 0) 0
  have h2 := Satisfies.imp_iff_imp.mp h1 (Satisfies.box_iff_forall.mpr fun w' hw' =>
    Satisfies.imp_iff_imp.mpr fun hb => by
      change w' = 0 + 1 ∧ 0 < 2 at hw'
      obtain ⟨rfl, _⟩ := hw'
      have := Satisfies.box_iff_forall.mp hb 2 ⟨rfl, by omega⟩
      change 2 = 0 at this
      omega)
  have := Satisfies.box_iff_forall.mp h2 1 ⟨rfl, by omega⟩
  change 1 = 0 at this
  omega

instance F1trans : IsTrans Unit F1.rel := ⟨fun _ _ _ _ _ => trivial⟩
instance MU1trans : IsTrans Unit MU1.rel := ⟨fun _ _ _ _ _ => trivial⟩

-- `Cslib.Logic.Modal.Satisfies.l` idx 7: necessary (reflexive point, φ = ⊥)
theorem u26 : ¬ drop0% Cslib.Logic.Modal.Satisfies.l 7 := fun h => by
  have h1 := (Satisfies.axiom_def _).mpr (h (τ := τU) F1 ff) (fun _ _ => False) ()
  have h2 := Satisfies.imp_iff_imp.mp h1 (Satisfies.box_iff_forall.mpr fun _ _ =>
    Satisfies.imp_iff_imp.mpr fun hb => Satisfies.box_iff_forall.mp hb () trivial)
  exact Satisfies.box_iff_forall.mp h2 () trivial

-- `Cslib.Logic.Modal.Satisfies.l_induction` idx 7: removable (plain well-founded induction along the converse relation; transitivity unused)
theorem u27 : drop% Cslib.Logic.Modal.Satisfies.l_induction 7 := by
  intro τ _ _ World Atom φ m hwf hstep w
  refine hwf.induction (C := fun w => Satisfies m w φ) w ?_
  intro w ih
  exact Satisfies.imp_iff_imp.mp (hstep w) (Satisfies.box_iff_forall.mpr fun w' hw' => ih w' hw')

-- `Cslib.Logic.Modal.Satisfies.l_induction` idx 8: necessary (reflexive point, φ = ⊥)
theorem u28 : ¬ drop0% Cslib.Logic.Modal.Satisfies.l_induction 8 := fun h =>
  h (τ := τU) (φ := ff) MU1 (fun _ => Satisfies.imp_iff_imp.mpr fun hb => Satisfies.box_iff_forall.mp hb () trivial) ()

instance MU0trans : IsTrans Unit MU0.rel := ⟨fun _ _ _ h _ => h⟩

-- `Cslib.Logic.Modal.Satisfies.l_induction` idx 9: necessary (empty frame, φ = ⊥)
theorem u29 : ¬ drop0% Cslib.Logic.Modal.Satisfies.l_induction 9 := fun h =>
  h (τ := τU) (φ := ff) MU0 ⟨fun a => ⟨a, fun _ h => h.elim⟩⟩ ()


/-- ℕ with < -/
def FLT : Frame ℕ τU := Frame.ofRelation (fun a b => a < b)
instance FLTtrans : IsTrans ℕ FLT.rel := ⟨fun _ _ _ (h1 : _ < _) (h2 : _ < _) => Nat.lt_trans h1 h2⟩
theorem FLTdiamond : Relation.Diamond FLT.rel := fun {_ b c} _ _ =>
  ⟨b + c + 1, show b < b + c + 1 by omega, show c < b + c + 1 by omega⟩
def pT : Logic.Modal.Proposition τU Bool := .atom true
def pF : Logic.Modal.Proposition τU Bool := .atom false

/-- generic refutation of ◇(φ₁ ∧ φ₂) ≡ ◇φ₁ ∧ ◇φ₂ at world 0 -/
theorem dae {m : Model ℕ τU Bool} (e : Logic.HasDiamond.diamond (Logic.HasAnd.and pT pF) ≡[Proposition.Equiv m]
      Logic.HasAnd.and (Logic.HasDiamond.diamond pT) (Logic.HasDiamond.diamond pF))
    (a b : ℕ) (ha : m.rel 0 a) (hb : m.rel 0 b) (hpa : m.v a true) (hpb : m.v b false)
    (hno : ∀ w, m.rel 0 w → m.v w true → m.v w false → False) : False := by
  have h1 := (Proposition.equiv_iff_forall_iff.mp e 0).mpr (Satisfies.and_iff_and.mpr
    ⟨Satisfies.diamond_iff_exists.mpr ⟨a, ha, hpa⟩, Satisfies.diamond_iff_exists.mpr ⟨b, hb, hpb⟩⟩)
  obtain ⟨w, hw, hs⟩ := Satisfies.diamond_iff_exists.mp h1
  exact hno w hw (Satisfies.and_iff_and.mp hs).1 (Satisfies.and_iff_and.mp hs).2

-- `Cslib.Logic.Modal.Proposition.diamond_and_equiv_of_preserves` idx 10: necessary ((ℕ, <), p only at 1, q at all n ≥ 2)
theorem d1 : ¬ drop0% Cslib.Logic.Modal.Proposition.diamond_and_equiv_of_preserves 10 := fun h =>
  dae (h (τ := τU) (m := ⟨FLT, fun n b => cond b (n = 1) (2 ≤ n)⟩) (φ₁ := pT) (φ₂ := pF) FLTdiamond
      (fun a b (hab : a < b) (ha : 2 ≤ a) => show 2 ≤ b by omega))
    1 2 (show 0 < 1 by omega) (show 0 < 2 by omega) rfl (show 2 ≤ 2 from le_rfl)
    (fun w _ (h1 : w = 1) (h2 : 2 ≤ w) => by omega)

-- `Cslib.Logic.Modal.Proposition.diamond_and_equiv_of_preserves` idx 11: necessary ((ℕ, <), p at all n ≥ 2, q only at 1)
theorem d2 : ¬ drop0% Cslib.Logic.Modal.Proposition.diamond_and_equiv_of_preserves 11 := fun h =>
  dae (h (τ := τU) (m := ⟨FLT, fun n b => cond b (2 ≤ n) (n = 1)⟩) (φ₁ := pT) (φ₂ := pF) FLTdiamond
      (fun a b (hab : a < b) (ha : 2 ≤ a) => show 2 ≤ b by omega))
    2 1 (show 0 < 2 by omega) (show 0 < 1 by omega) (show 2 ≤ 2 from le_rfl) rfl
    (fun w _ (h1 : 2 ≤ w) (h2 : w = 1) => by omega)

instance FPtrans : IsTrans ℕ FP.rel :=
  ⟨fun a b c (h1 : a = 0 ∧ (b = 1 ∨ b = 2)) (h2 : b = 0 ∧ (c = 1 ∨ c = 2)) => (by omega : False).elim⟩

-- `Cslib.Logic.Modal.Proposition.diamond_and_equiv_of_preserves` idx 9: necessary (0 → 1, 0 → 2, p at 1, q at 2)
theorem d3 : ¬ drop0% Cslib.Logic.Modal.Proposition.diamond_and_equiv_of_preserves 9 := fun h =>
  dae (h (τ := τU) (m := ⟨FP, fun n b => cond b (n = 1) (n = 2)⟩) (φ₁ := pT) (φ₂ := pF)
      (fun a b (hab : a = 0 ∧ _) (ha : a = 1) => by omega)
      (fun a b (hab : a = 0 ∧ _) (ha : a = 2) => by omega))
    1 2 ⟨rfl, Or.inl rfl⟩ ⟨rfl, Or.inr rfl⟩ rfl rfl
    (fun w _ (h1 : w = 1) (h2 : w = 2) => by omega)

/-- 0 → 1, 0 → 2, 1 → 3, 2 → 3, 3 → 3: diamond, not transitive -/
def FD : Frame ℕ τU := Frame.ofRelation (fun a b => (a = 0 ∧ (b = 1 ∨ b = 2)) ∨ (1 ≤ a ∧ a ≤ 3 ∧ b = 3))

-- `Cslib.Logic.Modal.Proposition.diamond_and_equiv_of_preserves` idx 6: necessary (0 → 1, 2 → 3 ↺ not transitive; p at 1, 3; q at 2, 3)
theorem d4 : ¬ drop0% Cslib.Logic.Modal.Proposition.diamond_and_equiv_of_preserves 6 := fun h =>
  dae (h (τ := τU) (m := ⟨FD, fun n b => cond b (n = 1 ∨ n = 3) (n = 2 ∨ n = 3)⟩) (φ₁ := pT) (φ₂ := pF)
      (fun {a b c} (h1 : (a = 0 ∧ (b = 1 ∨ b = 2)) ∨ (1 ≤ a ∧ a ≤ 3 ∧ b = 3))
        (h2 : (a = 0 ∧ (c = 1 ∨ c = 2)) ∨ (1 ≤ a ∧ a ≤ 3 ∧ c = 3)) =>
        ⟨3, show (b = 0 ∧ (3 = 1 ∨ 3 = 2)) ∨ (1 ≤ b ∧ b ≤ 3 ∧ 3 = 3) by omega,
          show (c = 0 ∧ (3 = 1 ∨ 3 = 2)) ∨ (1 ≤ c ∧ c ≤ 3 ∧ 3 = 3) by omega⟩)
      (fun a b (hab : (a = 0 ∧ (b = 1 ∨ b = 2)) ∨ (1 ≤ a ∧ a ≤ 3 ∧ b = 3)) (ha : a = 1 ∨ a = 3) =>
        show b = 1 ∨ b = 3 by omega)
      (fun a b (hab : (a = 0 ∧ (b = 1 ∨ b = 2)) ∨ (1 ≤ a ∧ a ≤ 3 ∧ b = 3)) (ha : a = 2 ∨ a = 3) =>
        show b = 2 ∨ b = 3 by omega))
    1 2 (Or.inl ⟨rfl, Or.inl rfl⟩) (Or.inl ⟨rfl, Or.inr rfl⟩) (Or.inl rfl) (Or.inl rfl)
    (fun w (hw : (0 = 0 ∧ (w = 1 ∨ w = 2)) ∨ (1 ≤ 0 ∧ 0 ≤ 3 ∧ w = 3)) (h1 : w = 1 ∨ w = 3)
      (h2 : w = 2 ∨ w = 3) => by omega)

/-- single edge 0 → 1 (transitive, not reflexive) -/
def F01 : Frame ℕ τU := Frame.ofRelation (fun a b => a = 0 ∧ b = 1)
instance F01trans : IsTrans ℕ F01.rel := ⟨fun a b c (h1 : a = 0 ∧ b = 1) (h2 : b = 0 ∧ c = 1) => (by omega : False).elim⟩
/-- n → n, n → n + 1 (reflexive, not transitive) -/
def FR : Frame ℕ τU := Frame.ofRelation (fun a b => b = a ∨ b = a + 1)
instance FRrefl : Std.Refl FR.rel := ⟨fun _ => Or.inl rfl⟩

-- `Cslib.Logic.Modal.Proposition.diamond_diamond_equiv` idx 6: necessary (single edge 0 → 1, atom at 1)
theorem d5 : ¬ drop0% Cslib.Logic.Modal.Proposition.diamond_diamond_equiv 6 := fun h => by
  have e := h (τ := τU) (m := ⟨F01, fun n _ => n = 1⟩) pa
  have h1 := (Proposition.equiv_iff_forall_iff.mp e 0).mpr (Satisfies.diamond_iff_exists.mpr ⟨1, ⟨rfl, rfl⟩, rfl⟩)
  obtain ⟨w, hw, h2⟩ := Satisfies.diamond_iff_exists.mp h1
  obtain ⟨_, hw', _⟩ := Satisfies.diamond_iff_exists.mp h2
  change 0 = 0 ∧ w = 1 at hw
  change w = 0 ∧ _ at hw'
  omega

-- `Cslib.Logic.Modal.Proposition.diamond_diamond_equiv` idx 7: necessary (n → n, n → n + 1; atom at 2)
theorem d6 : ¬ drop0% Cslib.Logic.Modal.Proposition.diamond_diamond_equiv 7 := fun h => by
  have e := h (τ := τU) (m := ⟨FR, fun n _ => n = 2⟩) pa
  have h1 := (Proposition.equiv_iff_forall_iff.mp e 0).mp (Satisfies.diamond_iff_exists.mpr
    ⟨1, Or.inr rfl, Satisfies.diamond_iff_exists.mpr ⟨2, Or.inr rfl, rfl⟩⟩)
  obtain ⟨w, hw, h2⟩ := Satisfies.diamond_iff_exists.mp h1
  change w = 0 ∨ w = 0 + 1 at hw
  change w = 2 at h2
  omega

end W1c5

namespace W1c5
open Cslib Logic.Modal

/-- states of an image-infinite LTS: s1 → b, a n (all n); s2 → a n; b →k d (all k); a n →k d (k < n) -/
inductive St | s1 | s2 | b | a (n : ℕ) | d

def T (s : St) (μ : Option ℕ) (t : St) : Prop :=
  match s, μ with
  | .s1, none => t = .b ∨ ∃ n, t = .a n
  | .s2, none => ∃ n, t = .a n
  | .b, some _ => t = .d
  | .a n, some k => k < n ∧ t = .d
  | _, _ => False

def MI : HML.Model St (Option ℕ) Empty := ⟨⟨T⟩, fun _ _ => False⟩

/-- for every proposition, a n agrees with b for all large n -/
theorem ev (ψ : HML.Proposition (Option ℕ) Empty) :
    ∃ N, ∀ n, N ≤ n → (Satisfies MI.toModal (.a n) ψ ↔ Satisfies MI.toModal .b ψ) := by
  induction ψ with
  | atom p => exact p.elim
  | false => exact ⟨0, fun _ _ => Iff.rfl⟩
  | not φ ih =>
    obtain ⟨N, hN⟩ := ih
    exact ⟨N, fun n hn => not_congr (hN n hn)⟩
  | or φ₁ φ₂ ih₁ ih₂ =>
    obtain ⟨N₁, h₁⟩ := ih₁
    obtain ⟨N₂, h₂⟩ := ih₂
    exact ⟨max N₁ N₂, fun n hn => or_congr (h₁ n (by omega)) (h₂ n (by omega))⟩
  | triangle op φs _ =>
    cases op with
    | none => exact ⟨0, fun n _ => ⟨fun ⟨_, hr, _⟩ => hr.elim, fun ⟨_, hr, _⟩ => hr.elim⟩⟩
    | some k =>
      refine ⟨k + 1, fun n hn => ⟨fun ⟨ws, hr, hs⟩ => ⟨ws, hr.2, hs⟩, fun ⟨ws, hr, hs⟩ => ⟨ws, ⟨by omega, hr⟩, hs⟩⟩⟩

/-- s1 and s2 have the same theory -/
theorem thEq (φ : HML.Proposition (Option ℕ) Empty) :
    Satisfies MI.toModal .s1 φ ↔ Satisfies MI.toModal .s2 φ := by
  induction φ with
  | atom p => exact p.elim
  | false => exact Iff.rfl
  | not φ ih => exact not_congr ih
  | or φ₁ φ₂ ih₁ ih₂ => exact or_congr ih₁ ih₂
  | triangle op φs _ =>
    cases op with
    | some k => exact ⟨fun ⟨_, hr, _⟩ => hr.elim, fun ⟨_, hr, _⟩ => hr.elim⟩
    | none =>
      constructor
      · rintro ⟨ws, hr, hs⟩
        rcases (hr : ws () = .b ∨ ∃ n, ws () = .a n) with h | ⟨n, h⟩
        · obtain ⟨N, hN⟩ := ev (φs ())
          refine ⟨fun _ => .a N, (⟨N, rfl⟩ : ∃ n, St.a N = .a n), fun i => ?_⟩
          have := hs ()
          rw [h] at this
          exact (hN N le_rfl).2 this
        · exact ⟨ws, (⟨n, h⟩ : ∃ n, ws () = .a n), hs⟩
      · rintro ⟨ws, ⟨n, h⟩, hs⟩
        exact ⟨ws, (Or.inr ⟨n, h⟩ : ws () = .b ∨ ∃ n, ws () = .a n), hs⟩

/-- no bisimulation relates s1 and s2 -/
theorem noBisim (r : St → St → Prop) (hr : MI.lts.IsHomBisimulation r) (h : r .s1 .s2) : False := by
  obtain ⟨s', hs', hbs⟩ := (hr h none).1 .b (Or.inl rfl)
  obtain ⟨n, rfl⟩ := (hs' : ∃ n, s' = .a n)
  obtain ⟨t, ht, _⟩ := (hr hbs (some n)).1 .d rfl
  exact absurd (ht : n < n ∧ t = .d).1 (Nat.lt_irrefl n)

theorem MIthEq : TheoryEq MI.toModal .s1 .s2 := Set.ext fun φ => thEq φ

-- `Cslib.Logic.Modal.theoryEq_isBisimulation` idx 4: necessary (image-infinite LTS: s1 → b, a n; s2 → a n; b →k d for all k, a n →k d for k < n; s1, s2 theory-equivalent, not bisimilar)
theorem t1 : ¬ drop0% Cslib.Logic.Modal.theoryEq_isBisimulation 4 := fun h =>
  noBisim _ (h (m := MI)) MIthEq

-- `Cslib.Logic.Modal.theoryEq_eq_bisimilarity` idx 4: necessary (same image-infinite LTS, no atoms)
theorem t2 : ¬ drop0% Cslib.Logic.Modal.theoryEq_eq_bisimilarity 4 := fun h => by
  have e := h (m := MI) (fun _ _ => Iff.rfl)
  have hb : LTS.HomBisimilarity MI.lts .s1 .s2 := (congrArg (fun f => f St.s1 St.s2) e).mp MIthEq
  obtain ⟨r, hr, hbis⟩ := hb
  exact noBisim r hbis hr

end W1c5
