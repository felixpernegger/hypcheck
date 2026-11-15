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

set_option linter.unusedSimpArgs false

-- ===== Circuits (Synthesis, Wire) =====
section Circ

namespace W2c3
open Cslib.Circuits

-- signature with one nullary op (interpreted as `true`) and one with one unary op
def σ1 : Signature := ⟨Unit, fun _ => 0⟩
def I1 : Interpretation σ1 Bool := fun _ _ => true
def σP (k : ℕ) : Signature := ⟨Unit, fun _ => k + 1⟩
def IP (k : ℕ) : Interpretation (σP k) Bool := fun _ v => v (Fin.last k)
abbrev σ2 := σP 0
abbrev I2 := IP 0
def cT : (Fin 0 → Bool) → Bool := fun _ => true
def cF : (Fin 0 → Bool) → Bool := fun _ => false

theorem cT_ne_cF : cT ≠ cF := fun h => by simpa [cT, cF] using congrFun h Fin.elim0

theorem av00 {σ : Signature} {U : Type} (I : Interpretation σ U) (p : Program σ 0 0) :
    available I p = ∅ := by
  ext f; simp only [available, Set.mem_range, Set.mem_empty_iff_false, iff_false]
  rintro ⟨w, -⟩; cases w with
  | input i => exact i.elim0
  | gate j => exact j.elim0

theorem ev1 : ∀ {g : ℕ} (p : Program σ1 0 g) (x : Fin 0 → Bool) (j : Fin g), p.eval I1 x j = true := by
  intro g p x j
  induction p with
  | empty => exact j.elim0
  | gate q line ih =>
    cases j using Fin.lastCases with
    | last => rw [Program.eval_gate_last]; rfl
    | cast k => rw [Program.eval_gate_castSucc]; exact ih k

theorem av1 {g : ℕ} (p : Program σ1 0 g) : available I1 p ⊆ {cT} := by
  intro f hf
  obtain ⟨w, hw⟩ := mem_available.mp hf
  cases w with
  | input i => exact i.elim0
  | gate j => funext x; rw [← hw x]; exact ev1 p x j

theorem evP (k : ℕ) : ∀ {g : ℕ} (p : Program (σP k) 1 g) (x : Fin 1 → Bool) (j : Fin g),
    p.eval (IP k) x j = x 0 := by
  intro g p x j
  induction p with
  | empty => exact j.elim0
  | gate q line ih =>
    cases j using Fin.lastCases with
    | last =>
      rw [Program.eval_gate_last]
      show Wire.elim x (q.eval (IP k) x) (line.wires (Fin.last k)) = x 0
      cases line.wires (Fin.last k) with
      | input i => rw [Subsingleton.elim i 0]; rfl
      | gate j => exact ih j
    | cast k => rw [Program.eval_gate_castSucc]; exact ih k

def π0 : (Fin 1 → Bool) → Bool := fun x => x 0

theorem synP {k : ℕ} {t : Set ((Fin 1 → Bool) → Bool)} {c : ℕ} {f} (hf : f ∈ t)
    (hf1 : f (fun _ => false) = true) : ¬ Synthesis (IP k) {π0} t c := by
  intro h
  obtain ⟨g, p, -, -, ht⟩ := h 0 .empty (fun _ h => by
    rw [Set.mem_singleton_iff.mp h]; exact inputs_subset_available (I := IP k) _ ⟨0, rfl⟩)
  obtain ⟨w, hw⟩ := mem_available.mp (ht hf)
  have := hw (fun _ => false)
  rw [hf1] at this
  cases w with
  | input i => exact absurd this (by simp [Program.trace, Wire.elim])
  | gate j => exact absurd this (by simp [Program.trace, Wire.elim, evP])

def σB : Signature := ⟨Bool, fun _ => 0⟩
def IB : Interpretation σB Bool := fun b _ => b

theorem synB (s : Set ((Fin 0 → Bool) → Bool)) (f : (Fin 0 → Bool) → Bool) : Synthesis IB s {f} 1 := by
  have e : f = fun _ => f Fin.elim0 := funext fun x => congrArg f (Subsingleton.elim _ _)
  rw [e]
  exact Synthesis.gate (I := IB) (s := s) (f Fin.elim0) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

theorem andMem (f g : (Fin 0 → Bool) → Bool) : (fun x => f x && g x) ∈ ({f, g} : Set _) := by
  have e : ∀ x : Fin 0 → Bool, x = Fin.elim0 := fun x => Subsingleton.elim _ _
  cases hf : f Fin.elim0
  · left; funext x; rw [e x, hf]; rfl
  · right; funext x; rw [e x, hf]; rfl

theorem wire2 : ∀ {g : ℕ} (p : Program σ2 0 g), IsEmpty (Wire 0 g) := by
  intro g p
  induction p with
  | empty => exact ⟨fun w => by cases w with | input i => exact i.elim0 | gate j => exact j.elim0⟩
  | gate q line ih => exact (ih.false (line.wires (0 : Fin 1))).elim

theorem synE {σ : Signature} {U : Type} {I : Interpretation σ U} {t : Set ((Fin 0 → U) → U)}
    {f : (Fin 0 → U) → U} (hf : f ∈ t) : ¬ Synthesis I ∅ t 0 := by
  intro h
  obtain ⟨g, p, hg, -, ht⟩ := h 0 .empty (Set.empty_subset _)
  obtain rfl : g = 0 := by omega
  simpa [av00] using ht hf

theorem synF {t : Set ((Fin 0 → Bool) → Bool)} {c : ℕ} (hf : cF ∈ t) : ¬ Synthesis I1 ∅ t c := by
  intro h
  obtain ⟨g, p, -, -, ht⟩ := h 0 .empty (Set.empty_subset _)
  exact cT_ne_cF (av1 p (ht hf)).symm

theorem syn2 {t : Set ((Fin 0 → Bool) → Bool)} {c : ℕ} {f} (hf : f ∈ t) : ¬ Synthesis I2 ∅ t c := by
  intro h
  obtain ⟨g, p, -, -, ht⟩ := h 0 .empty (Set.empty_subset _)
  obtain ⟨w, -⟩ := ht hf
  exact (wire2 p).false w

theorem synT {s : Set ((Fin 0 → Bool) → Bool)} : Synthesis I1 s {cT} 1 :=
  Synthesis.gate (I := I1) (s := s) (() : Unit) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

end W2c3

section CircV
open W2c3 Cslib.Circuits

-- `Cslib.Circuits.Synthesis.of_subset` idx 6: necessary (s = ∅, t = {cT}, n = 0)
theorem of_subset6 : ¬ drop0% Cslib.Circuits.Synthesis.of_subset 6 := fun h =>
  synE (I := I1) (Set.mem_singleton cT) (h (s := ∅))

-- `Cslib.Circuits.Synthesis.of_mem` idx 6: necessary (s = ∅, f = cT)
theorem of_mem6 : ¬ drop0% Cslib.Circuits.Synthesis.of_mem 6 := fun h =>
  synE (I := I1) (Set.mem_singleton cT) (h (s := ∅) (f := cT))

-- `Cslib.Circuits.Synthesis.mono` idx 8: necessary (s = s' = ∅, t = t' = {cF})
theorem mono8 : ¬ drop0% Cslib.Circuits.Synthesis.mono 8 := fun h =>
  synF (Set.mem_singleton cF) (@h σ1 Bool 0 I1 ∅ {cF} 0 0 ∅ {cF} subset_rfl subset_rfl le_rfl)

-- `Cslib.Circuits.Synthesis.mono` idx 11: necessary (s = {cF} ⊄ s' = ∅)
theorem mono11 : ¬ drop0% Cslib.Circuits.Synthesis.mono 11 := fun h =>
  synF (Set.mem_singleton cF) (@h σ1 Bool 0 I1 {cF} {cF} 0 0 (Synthesis.of_subset subset_rfl) ∅ {cF} subset_rfl le_rfl)

-- `Cslib.Circuits.Synthesis.mono` idx 12: necessary (t = ∅, t' = {cF})
theorem mono12 : ¬ drop0% Cslib.Circuits.Synthesis.mono 12 := fun h =>
  synF (Set.mem_singleton cF) (@h σ1 Bool 0 I1 ∅ ∅ 0 0 (Synthesis.of_subset subset_rfl) ∅ {cF} subset_rfl le_rfl)

-- `Cslib.Circuits.Synthesis.mono` idx 13: necessary (cT needs one gate, b = 0)
theorem mono13 : ¬ drop0% Cslib.Circuits.Synthesis.mono 13 := fun h =>
  synE (Set.mem_singleton cT) (@h σ1 Bool 0 I1 ∅ {cT} 1 0 synT ∅ {cT} subset_rfl subset_rfl)

-- `Cslib.Circuits.Synthesis.comp` idx 9: necessary
theorem comp9 : ¬ drop0% Cslib.Circuits.Synthesis.comp 9 := fun h =>
  synF (by simp) (@h σ1 Bool 0 I1 ∅ {cF} ∅ 0 0 (Synthesis.of_subset (Set.empty_subset _)))

-- `Cslib.Circuits.Synthesis.comp` idx 10: necessary
theorem comp10 : ¬ drop0% Cslib.Circuits.Synthesis.comp 10 := fun h =>
  synF (by simp) (@h σ1 Bool 0 I1 ∅ ∅ {cF} 0 0 (Synthesis.of_subset subset_rfl))

-- `Cslib.Circuits.Synthesis.trans` idx 9: necessary
theorem trans9 : ¬ drop0% Cslib.Circuits.Synthesis.trans 9 := fun h =>
  synF (Set.mem_singleton cF) (@h σ1 Bool 0 I1 ∅ {cF} {cF} 0 0 (Synthesis.of_subset (by simp)))

-- `Cslib.Circuits.Synthesis.trans` idx 10: necessary
theorem trans10 : ¬ drop0% Cslib.Circuits.Synthesis.trans 10 := fun h =>
  synF (Set.mem_singleton cF) (@h σ1 Bool 0 I1 ∅ ∅ {cF} 0 0 (Synthesis.of_subset subset_rfl))

-- `Cslib.Circuits.Synthesis.union` idx 9: necessary
theorem union9 : ¬ drop0% Cslib.Circuits.Synthesis.union 9 := fun h =>
  synF (by simp) (@h σ1 Bool 0 I1 ∅ {cF} ∅ 0 0 (Synthesis.of_subset subset_rfl))

-- `Cslib.Circuits.Synthesis.union` idx 10: necessary
theorem union10 : ¬ drop0% Cslib.Circuits.Synthesis.union 10 := fun h =>
  synF (by simp) (@h σ1 Bool 0 I1 ∅ ∅ {cF} 0 0 (Synthesis.of_subset subset_rfl))

-- `Cslib.Circuits.Synthesis.gate` idx 7: necessary (unary op, no wire available for n = 0)
theorem gate7 : ¬ drop0% Cslib.Circuits.Synthesis.gate 7 := fun h =>
  syn2 (Set.mem_singleton _) (@h σ2 Bool 0 I2 ∅ () (fun _ => cF))

-- `Cslib.Circuits.Synthesis.biUnion` idx 9: necessary
theorem biUnion9 : ¬ drop0% Cslib.Circuits.Synthesis.biUnion 9 := fun h =>
  synF (by simp) (@h σ1 Bool 0 Unit I1 ∅ {()} (fun _ => {cF}) (fun _ => 0))

-- `Cslib.Circuits.Synthesis.iUnion` idx 9: necessary
theorem iUnion9 : ¬ drop0% Cslib.Circuits.Synthesis.iUnion 9 := fun h =>
  synF (by simp) (@h σ1 Bool 0 Unit I1 ∅ _ (fun _ => {cF}) (fun _ => 0))

-- `Cslib.Circuits.Synthesis.family` idx 9: necessary
theorem family9 : ¬ drop0% Cslib.Circuits.Synthesis.family 9 := fun h =>
  synF (Set.mem_range_self ()) (@h σ1 Bool 0 Unit I1 ∅ _ (fun _ => cF) (fun _ => 0))

-- `Cslib.Circuits.Synthesis.gate_of_syntheses` idx 8: necessary
theorem gate_of_syntheses8 : ¬ drop0% Cslib.Circuits.Synthesis.gate_of_syntheses 8 := fun h =>
  syn2 (Set.mem_singleton _) (@h σ2 Bool 0 I2 ∅ () (fun _ => cF) (fun _ => 0))

-- `Cslib.Circuits.Synthesis.nullary` idx 6: necessary (dependent; unary op)
theorem nullary6 : ¬ indep0% Cslib.Circuits.Synthesis.nullary 6 := fun h =>
  absurd (@h σ2 Bool 0 I2 ∅ ()) (by decide)

-- `Cslib.Circuits.Synthesis.unary` idx 7: necessary
theorem unary7 : ¬ drop0% Cslib.Circuits.Synthesis.unary 7 := fun h =>
  syn2 (Set.mem_singleton _) (@h σ2 Bool 0 I2 ∅ 0 cF ())

-- `Cslib.Circuits.Synthesis.binary` idx 9: necessary
theorem binary9 : ¬ drop0% Cslib.Circuits.Synthesis.binary 9 := fun h =>
  synP (Set.mem_singleton _) (by simp [IP, σP]) (@h (σP 0) Bool 1 (IP 0) {π0} 0 0 (fun _ => true) π0 (Synthesis.of_subset subset_rfl) ())

-- `Cslib.Circuits.Synthesis.binary` idx 10: necessary
theorem binary10 : ¬ drop0% Cslib.Circuits.Synthesis.binary 10 := fun h =>
  synP (Set.mem_singleton _) (by simp [IP, σP]) (@h (σP 1) Bool 1 (IP 1) {π0} 0 0 π0 (fun _ => true) (Synthesis.of_subset subset_rfl) ())

-- `Cslib.Circuits.Synthesis.combine` idx 11: necessary (g = cT, f = result = cF)
theorem combine11 : ¬ drop0% Cslib.Circuits.Synthesis.combine 11 := fun h =>
  synF (Set.mem_singleton cF) (@h σ1 Bool 0 I1 ∅ 0 1 cF cT cF 0 synT (Synthesis.of_subset (by simp)))

-- `Cslib.Circuits.Synthesis.combine` idx 12: necessary (f = cT, g = result = cF)
theorem combine12 : ¬ drop0% Cslib.Circuits.Synthesis.combine 12 := fun h =>
  synF (Set.mem_singleton cF) (@h σ1 Bool 0 I1 ∅ 1 0 cT cF cF 0 synT (Synthesis.of_subset (by simp)))

-- `Cslib.Circuits.Synthesis.combine` idx 13: necessary (f = g = cT, result = cF)
theorem combine13 : ¬ drop0% Cslib.Circuits.Synthesis.combine 13 := fun h =>
  synF (Set.mem_singleton cF) (@h σ1 Bool 0 I1 ∅ 1 1 cT cT cF 0 synT synT)

-- `Cslib.Circuits.Synthesis.foldr` idx 9: necessary (op = const false)
theorem foldr9 : ¬ drop0% Cslib.Circuits.Synthesis.foldr 9 := fun h =>
  synF (Set.mem_singleton_iff.mpr rfl)
    (@h σ1 Bool 0 Unit I1 ∅ 1 (fun _ _ => false) 0 [()] (fun _ => cT) (fun _ => 1) cT synT (fun _ _ => synT))

-- `Cslib.Circuits.Synthesis.foldr` idx 14: necessary (op = left projection, seed = cF)
theorem foldr14 : ¬ drop0% Cslib.Circuits.Synthesis.foldr 14 := fun h =>
  synF (Set.mem_singleton_iff.mpr rfl)
    (@h σ1 Bool 0 Unit I1 ∅ 0 (fun a _ => a) 0 (fun _ _ => Synthesis.of_subset (by simp)) [] (fun _ => cT) (fun _ => 1) cF
      (fun _ h => nomatch h))

-- `Cslib.Circuits.Synthesis.foldr` idx 15: necessary (op = left projection, f () = cF)
theorem foldr15 : ¬ drop0% Cslib.Circuits.Synthesis.foldr 15 := fun h =>
  synF (Set.mem_singleton_iff.mpr rfl)
    (@h σ1 Bool 0 Unit I1 ∅ 1 (fun a _ => a) 0 (fun _ _ => Synthesis.of_subset (by simp)) [()] (fun _ => cF) (fun _ => 0) cT
      synT)

instance : Std.Commutative (fun (_ _ : Bool) => false) := ⟨fun _ _ => rfl⟩
instance : Std.Associative (fun (_ _ : Bool) => false) := ⟨fun _ _ _ => rfl⟩
instance : Std.Commutative (fun (_ _ : Bool) => true) := ⟨fun _ _ => rfl⟩
instance : Std.Associative (fun (_ _ : Bool) => true) := ⟨fun _ _ _ => rfl⟩

-- `Cslib.Circuits.Synthesis.finset_fold` idx 8: necessary (dependent; left projection is associative, not commutative)
theorem finset_fold8 : ¬ indep0% Cslib.Circuits.Synthesis.finset_fold 8 := fun h =>
  absurd ((@h σB Bool 0 Unit IB ∅ 1 (fun a _ => a) ⟨fun _ _ _ => rfl⟩ 1 (fun _ _ => synB _ _) ∅ (fun _ => cT)
    (fun _ => 1) cT (synB _ _) (fun _ h => nomatch h)).comm true false) (by decide)

-- `Cslib.Circuits.Synthesis.finset_fold` idx 9: necessary (dependent; nand is commutative, not associative)
theorem finset_fold9 : ¬ indep0% Cslib.Circuits.Synthesis.finset_fold 9 := fun h =>
  absurd ((@h σB Bool 0 Unit IB ∅ 1 (fun a b => !(a && b)) ⟨by decide⟩ 1 (fun _ _ => synB _ _) ∅ (fun _ => cT)
    (fun _ => 1) cT (synB _ _) (fun _ h => nomatch h)).assoc true true false) (by decide)

-- `Cslib.Circuits.Synthesis.finset_fold` idx 11: necessary (op = const false)
theorem finset_fold11 : ¬ drop0% Cslib.Circuits.Synthesis.finset_fold 11 := fun h =>
  synF (Set.mem_singleton_iff.mpr rfl)
    (@h σ1 Bool 0 Unit I1 ∅ 1 (fun _ _ => false) _ _ 0 {()} (fun _ => cT) (fun _ => 1) cT synT (fun _ _ => synT))

-- `Cslib.Circuits.Synthesis.finset_fold` idx 16: necessary (op = const true, no indices, seed = cF)
theorem finset_fold16 : ¬ drop0% Cslib.Circuits.Synthesis.finset_fold 16 := fun h =>
  synF (Set.mem_singleton_iff.mpr rfl)
    (@h σ1 Bool 0 Unit I1 ∅ 0 (fun _ _ => true) _ _ 1 (fun _ _ => synT) ∅ (fun _ => cT) (fun _ => 1) cF
      (fun _ h => nomatch h))

-- `Cslib.Circuits.Synthesis.finset_fold` idx 17: necessary (op = and, f () = cF, seed = cT)
theorem finset_fold17 : ¬ drop0% Cslib.Circuits.Synthesis.finset_fold 17 := fun h =>
  synF (Set.mem_singleton_iff.mpr rfl)
    (@h σ1 Bool 0 Unit I1 ∅ 1 (· && ·) _ _ 0 (fun f g => Synthesis.of_subset (Set.singleton_subset_iff.mpr (andMem f g)))
      {()} (fun _ => cF) (fun _ => 0) cT synT)

-- `Cslib.Circuits.Synthesis.exists_circuit_outputs` idx 7: necessary (no wire for n = 0 and a unary op)
theorem exists_circuit_outputs7 : ¬ drop0% Cslib.Circuits.Synthesis.exists_circuit_outputs 7 := fun h => by
  obtain ⟨c, -, -⟩ := @h σ2 Bool 0 I2 1 0 (fun _ => cF)
  exact (wire2 c.program).false (c.outputs 0)

-- `Cslib.Circuits.Synthesis.exists_circuit` idx 6: necessary
theorem exists_circuit6 : ¬ drop0% Cslib.Circuits.Synthesis.exists_circuit 6 := fun h => by
  obtain ⟨c, -, -⟩ := @h σ2 Bool 0 I2 cF 0
  exact (wire2 c.program).false (c.outputs 0)

-- `Cslib.Circuits.Wire.Renaming.value_apply` idx 8: necessary (identity renaming, different gate values)
theorem value_apply8 : ¬ drop0% Cslib.Circuits.Wire.Renaming.value_apply 8 := fun h =>
  absurd (@h 0 1 1 Bool Wire.Renaming.id Fin.elim0 (fun _ => true) (fun _ => false) (.gate 0)) (by decide)

end CircV
end Circ

-- ===== Distributed consistency =====
section DC

namespace W2c3
open Cslib.DistributedConsistency

theorem tgT {r : Bool → Bool → Prop} (ht : ∀ a b c, r a b → r b c → r a c) {a b : Bool}
    (h : Relation.TransGen r a b) : r a b := by
  induction h with
  | single h => exact h
  | tail _ h ih => exact ht _ _ _ ih h

-- abstract execution on Bool, one session: rb = fun a b => a = false ∧ b = true, vis = fun _ _ => False, ar = fun a b => a = false ∧ b = true
def aeB : AbstractExecution Bool Unit Unit Unit where
  op _ := ()
  se _ := ()
  rval _ := some ()
  rb := fun a b => a = false ∧ b = true
  rb_strict_order := { irrefl := by decide, trans := by decide }
  rb_pred_finite _ := Set.toFinite _
  rb_interval_order := ⟨{ irrefl := by decide, trans := by decide }, by decide⟩
  rb_rval_ne_none _ _ _ := by simp
  so_strict_total_order u := by
    cases u
    exact {
      trichotomous := by
        rintro ⟨a, -⟩ ⟨b, -⟩
        simp only [BaseHistory.so, Relation.restrict, Set.mem_ofPred_eq, Subtype.mk.injEq, true_and]
        revert a b; decide
      irrefl := by
        rintro ⟨a, -⟩
        simp only [BaseHistory.so, Relation.restrict, Set.mem_ofPred_eq, true_and]
        revert a; decide
      trans := by
        rintro ⟨a, -⟩ ⟨b, -⟩ ⟨c, -⟩
        simp only [BaseHistory.so, Relation.restrict, Set.mem_ofPred_eq, true_and]
        revert a b c; decide }
  vis := fun _ _ => False
  ar := fun a b => a = false ∧ b = true
  vis_acyclic := ⟨fun a h => by
    cases h with
    | single h => exact h
    | tail _ h => exact h⟩
  vis_pred_finite _ := Set.toFinite _
  ar_strict_total_order := { irrefl := by decide, trans := by decide, trichotomous := by decide }

-- abstract execution on Bool, one session: rb = fun a b => a = false ∧ b = true, vis = fun a b => a = true ∧ b = false, ar = fun a b => a = true ∧ b = false
def aeR : AbstractExecution Bool Unit Unit Unit where
  op _ := ()
  se _ := ()
  rval _ := some ()
  rb := fun a b => a = false ∧ b = true
  rb_strict_order := { irrefl := by decide, trans := by decide }
  rb_pred_finite _ := Set.toFinite _
  rb_interval_order := ⟨{ irrefl := by decide, trans := by decide }, by decide⟩
  rb_rval_ne_none _ _ _ := by simp
  so_strict_total_order u := by
    cases u
    exact {
      trichotomous := by
        rintro ⟨a, -⟩ ⟨b, -⟩
        simp only [BaseHistory.so, Relation.restrict, Set.mem_ofPred_eq, Subtype.mk.injEq, true_and]
        revert a b; decide
      irrefl := by
        rintro ⟨a, -⟩
        simp only [BaseHistory.so, Relation.restrict, Set.mem_ofPred_eq, true_and]
        revert a; decide
      trans := by
        rintro ⟨a, -⟩ ⟨b, -⟩ ⟨c, -⟩
        simp only [BaseHistory.so, Relation.restrict, Set.mem_ofPred_eq, true_and]
        revert a b c; decide }
  vis := fun a b => a = true ∧ b = false
  ar := fun a b => a = true ∧ b = false
  vis_acyclic := ⟨fun x h => absurd (tgT (r := fun a b => a = true ∧ b = false) (by decide) h) (by cases x <;> decide)⟩
  vis_pred_finite _ := Set.toFinite _
  ar_strict_total_order := { irrefl := by decide, trans := by decide, trichotomous := by decide }

-- abstract execution on Bool, one session: rb = fun a b => a = false ∧ b = true, vis = fun a b => a = false ∧ b = true, ar = fun a b => a = true ∧ b = false
def aeV : AbstractExecution Bool Unit Unit Unit where
  op _ := ()
  se _ := ()
  rval _ := some ()
  rb := fun a b => a = false ∧ b = true
  rb_strict_order := { irrefl := by decide, trans := by decide }
  rb_pred_finite _ := Set.toFinite _
  rb_interval_order := ⟨{ irrefl := by decide, trans := by decide }, by decide⟩
  rb_rval_ne_none _ _ _ := by simp
  so_strict_total_order u := by
    cases u
    exact {
      trichotomous := by
        rintro ⟨a, -⟩ ⟨b, -⟩
        simp only [BaseHistory.so, Relation.restrict, Set.mem_ofPred_eq, Subtype.mk.injEq, true_and]
        revert a b; decide
      irrefl := by
        rintro ⟨a, -⟩
        simp only [BaseHistory.so, Relation.restrict, Set.mem_ofPred_eq, true_and]
        revert a; decide
      trans := by
        rintro ⟨a, -⟩ ⟨b, -⟩ ⟨c, -⟩
        simp only [BaseHistory.so, Relation.restrict, Set.mem_ofPred_eq, true_and]
        revert a b c; decide }
  vis := fun a b => a = false ∧ b = true
  ar := fun a b => a = true ∧ b = false
  vis_acyclic := ⟨fun x h => absurd (tgT (r := fun a b => a = false ∧ b = true) (by decide) h) (by cases x <;> decide)⟩
  vis_pred_finite _ := Set.toFinite _
  ar_strict_total_order := { irrefl := by decide, trans := by decide, trichotomous := by decide }

-- abstract execution on Bool, one session: rb = fun a b => a = true ∧ b = false, vis = fun a b => a = false ∧ b = true, ar = fun a b => a = false ∧ b = true
def aeM : AbstractExecution Bool Unit Unit Unit where
  op _ := ()
  se _ := ()
  rval _ := some ()
  rb := fun a b => a = true ∧ b = false
  rb_strict_order := { irrefl := by decide, trans := by decide }
  rb_pred_finite _ := Set.toFinite _
  rb_interval_order := ⟨{ irrefl := by decide, trans := by decide }, by decide⟩
  rb_rval_ne_none _ _ _ := by simp
  so_strict_total_order u := by
    cases u
    exact {
      trichotomous := by
        rintro ⟨a, -⟩ ⟨b, -⟩
        simp only [BaseHistory.so, Relation.restrict, Set.mem_ofPred_eq, Subtype.mk.injEq, true_and]
        revert a b; decide
      irrefl := by
        rintro ⟨a, -⟩
        simp only [BaseHistory.so, Relation.restrict, Set.mem_ofPred_eq, true_and]
        revert a; decide
      trans := by
        rintro ⟨a, -⟩ ⟨b, -⟩ ⟨c, -⟩
        simp only [BaseHistory.so, Relation.restrict, Set.mem_ofPred_eq, true_and]
        revert a b c; decide }
  vis := fun a b => a = false ∧ b = true
  ar := fun a b => a = false ∧ b = true
  vis_acyclic := ⟨fun x h => absurd (tgT (r := fun a b => a = false ∧ b = true) (by decide) h) (by cases x <;> decide)⟩
  vis_pred_finite _ := Set.toFinite _
  ar_strict_total_order := { irrefl := by decide, trans := by decide, trichotomous := by decide }

-- one event that never returns, in session false
def aeN : AbstractExecution Unit Unit Unit Bool where
  op _ := ()
  se _ := false
  rval _ := none
  rb _ _ := False
  rb_strict_order := { irrefl := fun _ h => h, trans := fun _ _ _ h _ => h }
  rb_pred_finite _ := Set.toFinite _
  rb_interval_order := ⟨{ irrefl := fun _ h => h, trans := fun _ _ _ h _ => h }, fun _ _ _ _ h => h.1.elim⟩
  rb_rval_ne_none _ _ h := h.elim
  so_strict_total_order s := {
      trichotomous := fun ⟨(), _⟩ ⟨(), _⟩ _ _ => rfl
      irrefl := fun _ h => h.2.2
      trans := fun _ _ _ h _ => h.2.2.elim }
  vis _ _ := False
  ar _ _ := False
  vis_acyclic := ⟨fun a h => by
    cases h with
    | single h => exact h
    | tail _ h => exact h⟩
  vis_pred_finite _ := Set.toFinite _
  ar_strict_total_order := { irrefl := fun _ h => h, trans := fun _ _ _ h _ => h, trichotomous := fun _ _ _ _ => rfl }

-- three events in separate sessions, rb empty, vis = successor (not transitive)
def aeT : AbstractExecution (Fin 3) Unit Unit (Fin 3) where
  op _ := ()
  se x := x
  rval _ := some ()
  rb _ _ := False
  rb_strict_order := { irrefl := fun _ h => h, trans := fun _ _ _ h _ => h }
  rb_pred_finite _ := Set.toFinite _
  rb_interval_order := ⟨{ irrefl := fun _ h => h, trans := fun _ _ _ h _ => h }, fun _ _ _ _ h => h.1.elim⟩
  rb_rval_ne_none _ _ h := h.elim
  so_strict_total_order s := {
      trichotomous := fun ⟨a, ha⟩ ⟨b, hb⟩ _ _ => Subtype.ext ((show a = s from ha).trans (show b = s from hb).symm)
      irrefl := fun _ h => h.2.2
      trans := fun _ _ _ h _ => h.2.2.elim }
  vis a b := b.val = a.val + 1
  ar a b := a < b
  vis_acyclic := ⟨fun x h => by
    have : ∀ a b, Relation.TransGen (fun a b : Fin 3 => b.val = a.val + 1) a b → a.val < b.val := by
      intro a b h; induction h with
      | single h => omega
      | tail _ h ih => omega
    exact lt_irrefl _ (this x x h)⟩
  vis_pred_finite _ := Set.toFinite _
  ar_strict_total_order := inferInstance

-- events ℕ, one session, rb = ar = <, vis empty
def aeNat : AbstractExecution ℕ Unit Unit Unit where
  op _ := ()
  se _ := ()
  rval _ := some ()
  rb := (· < ·)
  rb_strict_order := inferInstance
  rb_pred_finite x := Set.finite_Iio x
  rb_interval_order := ⟨inferInstance, fun a1 b1 a2 b2 h => by omega⟩
  rb_rval_ne_none _ _ _ := by simp
  so_strict_total_order u := by
    cases u
    exact {
      trichotomous := by
        rintro ⟨a, -⟩ ⟨b, -⟩
        simp only [BaseHistory.so, Relation.restrict, Set.mem_ofPred_eq, Subtype.mk.injEq, true_and]
        omega
      irrefl := by
        rintro ⟨a, -⟩
        simp [BaseHistory.so, Relation.restrict]
      trans := by
        rintro ⟨a, -⟩ ⟨b, -⟩ ⟨c, -⟩
        simp only [BaseHistory.so, Relation.restrict, Set.mem_ofPred_eq, true_and]
        omega }
  vis _ _ := False
  ar := (· < ·)
  vis_acyclic := ⟨fun a h => by
    cases h with
    | single h => exact h
    | tail _ h => exact h⟩
  vis_pred_finite _ := Set.finite_empty.subset (fun _ h => h.elim)
  ar_strict_total_order := inferInstance

def dB : ReplicatedDataType Bool Unit Unit := ⟨fun _ _ => none, fun _ _ _ _ => rfl⟩

theorem soB {a : AbstractExecution Bool Unit Unit Unit} {x y : Bool} (h : a.rb x y) : a.so () x y := ⟨rfl, rfl, h⟩

theorem hbC : aeM.hb false false := by
  unfold AbstractExecution.hb
  exact .tail (.single (Or.inl ⟨rfl, rfl⟩)) (Or.inr ⟨(), soB ⟨rfl, rfl⟩⟩)

end W2c3

section DCV
open W2c3 Cslib.DistributedConsistency AbstractExecution

-- `Cslib.DistributedConsistency.se_rval_eq_none` idx 7: necessary (x in session false, s = true)
theorem se7 : ¬ drop0% Cslib.DistributedConsistency.se_rval_eq_none 7 := fun h => by
  have := congrArg (() ∈ ·) (@h Unit Unit Unit Bool aeN true () rfl)
  simp [aeN] at this

-- `Cslib.DistributedConsistency.se_rval_eq_none` idx 8: necessary (aeB, x = false returns)
theorem se8 : ¬ drop0% Cslib.DistributedConsistency.se_rval_eq_none 8 := fun h => by
  have := congrArg (true ∈ ·) (@h Bool Unit Unit Unit aeB () false rfl)
  simp [aeB] at this

-- `Cslib.DistributedConsistency.singleOrder_vis_ar_rval_ne_none` idx 5: necessary (aeB)
theorem sovar5 : ¬ drop0% Cslib.DistributedConsistency.singleOrder_vis_ar_rval_ne_none 5 := fun h =>
  (@h Bool Unit Unit Unit aeB false true).2 ⟨rfl, rfl⟩ (by simp [aeB])

-- `Cslib.DistributedConsistency.singleOrder_realTime_imp_readMyWrites` idx 6: necessary (aeR: vis = ar reversed rb)
theorem sor6 : ¬ drop0% Cslib.DistributedConsistency.singleOrder_realTime_imp_readMyWrites 6 := fun h => by
  have := @h Bool Unit Unit Unit aeR ⟨∅, by simp, fun _ _ => by simp [aeR]⟩ () false true (soB ⟨rfl, rfl⟩)
  simp [aeR] at this

-- `Cslib.DistributedConsistency.linearizability_imp_sequentialConsistency` idx 6: necessary (aeB not SingleOrder)
theorem lin6 : ¬ drop0% Cslib.DistributedConsistency.linearizability_imp_sequentialConsistency 6 := fun h => by
  obtain ⟨⟨xs, hxs, hv⟩, -⟩ := @h Bool Unit Unit Unit dB aeB
  have := (hv false true).2 ⟨⟨rfl, rfl⟩, fun hx => by simpa [aeB] using hxs false hx⟩
  exact this

-- `Cslib.DistributedConsistency.singleOrder_readMyWrites_imp_causalArbitration` idx 5: necessary (aeV)
theorem sorca5 : ¬ drop0% Cslib.DistributedConsistency.singleOrder_readMyWrites_imp_causalArbitration 5 := fun h => by
  have := @h Bool Unit Unit Unit aeV (fun _ x y hs => hs.2.2) false true (.single (Or.inl ⟨rfl, rfl⟩))
  simp [aeV] at this

-- `Cslib.DistributedConsistency.singleOrder_readMyWrites_imp_causalArbitration` idx 6: necessary (aeR)
theorem sorca6 : ¬ drop0% Cslib.DistributedConsistency.singleOrder_readMyWrites_imp_causalArbitration 6 := fun h => by
  have := @h Bool Unit Unit Unit aeR ⟨∅, by simp, fun _ _ => by simp [aeR]⟩ false true
    (.single (Or.inr ⟨(), soB ⟨rfl, rfl⟩⟩))
  simp [aeR] at this

-- `Cslib.DistributedConsistency.causalVisibility_imp_readMyWrites` idx 5: necessary (aeB)
theorem cvrmw5 : ¬ drop0% Cslib.DistributedConsistency.causalVisibility_imp_readMyWrites 5 := fun h =>
  @h Bool Unit Unit Unit aeB () false true (soB ⟨rfl, rfl⟩)

-- `Cslib.DistributedConsistency.causalVisibility_imp_monotonicReads` idx 5: necessary (aeM: vis false true, so true false)
theorem cvmr5 : ¬ drop0% Cslib.DistributedConsistency.causalVisibility_imp_monotonicReads 5 := fun h => by
  have := @h Bool Unit Unit Unit aeM () false true false ⟨rfl, rfl⟩ (soB ⟨rfl, rfl⟩)
  simp [aeM] at this

-- `Cslib.DistributedConsistency.causalVisibility_imp_noCircularCausality` idx 5: necessary (aeM: hb cycle)
theorem cvncc5 : ¬ drop0% Cslib.DistributedConsistency.causalVisibility_imp_noCircularCausality 5 := fun h =>
  (@h Bool Unit Unit Unit aeM).irrefl false (.single hbC)

-- `Cslib.DistributedConsistency.singleOrder_readMyWrites_imp_causalVisibility` idx 5: necessary (aeT: vis not transitive)
theorem sorcv5 : ¬ drop0% Cslib.DistributedConsistency.singleOrder_readMyWrites_imp_causalVisibility 5 := fun h => by
  have := @h (Fin 3) Unit Unit (Fin 3) aeT (fun _ x y hs => hs.2.2.elim) 0 2
    (.tail (.single (Or.inl (show (1 : Fin 3).val = (0 : Fin 3).val + 1 from rfl)))
      (Or.inl (show (2 : Fin 3).val = (1 : Fin 3).val + 1 from rfl)))
  exact absurd this (by simp [aeT])

-- `Cslib.DistributedConsistency.singleOrder_readMyWrites_imp_causalVisibility` idx 6: necessary (aeR)
theorem sorcv6 : ¬ drop0% Cslib.DistributedConsistency.singleOrder_readMyWrites_imp_causalVisibility 6 := fun h => by
  have := @h Bool Unit Unit Unit aeR ⟨∅, by simp, fun _ _ => by simp [aeR]⟩ false true
    (.single (Or.inr ⟨(), soB ⟨rfl, rfl⟩⟩))
  simp [aeR] at this

-- `Cslib.DistributedConsistency.singleOrder_imp_eventualVisibility` idx 5: necessary (aeNat: nothing visible)
theorem soev5 : ¬ drop0% Cslib.DistributedConsistency.singleOrder_imp_eventualVisibility 5 := fun h => by
  have := @h ℕ Unit Unit Unit aeNat 0 ()
  have e : aeNat.nonVisibleEvents 0 () = Set.Ioi 0 := by
    ext y; simp [nonVisibleEvents, aeNat]
  rw [e] at this
  exact Set.Ioi_infinite 0 this

-- `Cslib.DistributedConsistency.sequentialConsistency_imp_causalConsistency` idx 6: necessary (aeB not causal)
theorem sccc6 : ¬ drop0% Cslib.DistributedConsistency.sequentialConsistency_imp_causalConsistency 6 := fun h =>
  (@h Bool Unit Unit Unit dB aeB).2.1.2 false true (.single (Or.inr ⟨(), soB ⟨rfl, rfl⟩⟩))

-- `Cslib.DistributedConsistency.causalConsistency_imp_basicEventualConsistency` idx 6: necessary (aeM: hb cycle)
theorem ccbec6 : ¬ drop0% Cslib.DistributedConsistency.causalConsistency_imp_basicEventualConsistency 6 := fun h =>
  (@h Bool Unit Unit Unit dB aeM).2.1.irrefl false (.single hbC)

-- `Cslib.DistributedConsistency.History.rb_rval_ne_none` idx 7: necessary (aeN: an event that never returns)
theorem rbr7 : ¬ drop0% Cslib.DistributedConsistency.History.rb_rval_ne_none 7 := fun h =>
  @h Unit Unit Unit Bool aeN.toHistory () () rfl

end DCV
end DC

-- ===== FLP =====
section FLPS

namespace W2c3
open Cslib Cslib.FLP

def flpA : Algorithm Unit Unit Unit := ⟨fun _ => (), fun _ _ => (), fun _ _ => 0, fun _ _ => none⟩
def flpS0 : State Unit Unit Unit := ⟨0, fun _ => ⟨(), none⟩⟩
def m1 : Message Unit Unit := ⟨(), .inl true⟩
def flpS1 : State Unit Unit Unit := ⟨{m1}, fun _ => ⟨(), none⟩⟩
def flpSd : State Unit Unit Unit := ⟨0, fun _ => ⟨(), some true⟩⟩

theorem rA : flpA.recvMsg m1 flpS1 = flpS0 := by
  unfold Algorithm.recvMsg
  simp only [flpA, flpS0, flpS1, m1, Cslib.FLP.State.mk.injEq]
  refine ⟨by simp, ?_⟩
  funext q; simp

theorem trA : flpA.lts.Tr flpS1 (some m1) flpS0 := ⟨by simp [flpS1], rA.symm⟩

theorem flpCrvStay {P M S : Type} [DecidableEq P] [DecidableEq M] (a : Algorithm P M S)
    {ps : Set P} (hps : ∀ p, p ∉ ps) {s t : State P M S} (h : a.CanReachVia ps s t) :
    t = s := by
  induction h with
  | refl => rfl
  | tail _ hst ih =>
    obtain ⟨x, hx, ht⟩ := hst
    subst ih
    cases x with
    | none => exact ht
    | some m => exact absurd hx (hps _)

-- an algorithm that never decides keeps every `out` field `none`
theorem noOut {P M S : Type} [DecidableEq P] [DecidableEq M] {a : Algorithm P M S}
    (hout : ∀ m q, a.out m q = none) {s t : State P M S} {xl : List (Action P M)}
    (h : a.lts.MTr s xl t) (hs : ∀ p, (s.proc p).out = none) : ∀ p, (t.proc p).out = none := by
  induction h with
  | refl => exact hs
  | @stepL s1 x s2 xl t htr _ ih =>
    apply ih
    cases x with
    | none => cases htr; exact hs
    | some m =>
      obtain ⟨-, rfl⟩ := htr
      intro p
      simp only [Algorithm.recvMsg]
      split
      · simp [hs, hout]
      · exact hs p

theorem flpA_noDec {s : State Unit Unit Unit} (h : flpA.lts.CanReach flpS0 s) : (s.proc ()).out = none := by
  obtain ⟨xl, h⟩ := h
  exact noOut (fun _ _ => rfl) h (fun _ => rfl) ()

theorem flpA_noDecS {s : State Unit Unit Unit} {inp} (h : flpA.Reachable inp s) : (s.proc ()).out = none := by
  obtain ⟨xl, h⟩ := h
  exact noOut (fun _ _ => rfl) h (fun _ => rfl) ()

def sqS (s0 s1 : State Unit Unit Unit) : ωSequence (State Unit Unit Unit) := ⟨fun n => if n = 0 then s0 else s1⟩
def sqA (x0 x1 : Action Unit Unit) : ωSequence (Action Unit Unit) := ⟨fun n => if n = 0 then x0 else x1⟩


-- flpI: decides its input on its first message
def flpI : Algorithm Unit Unit Unit :=
  ⟨fun _ => (), fun _ _ => (), fun _ _ => 0, fun m _ => match m.msg with | .inl b => some b | .inr _ => none⟩

-- from the all-false start, flpI never decides true
theorem flpI_inv {s t : State Unit Unit Unit} {xl : List (Action Unit Unit)} (h : flpI.lts.MTr s xl t)
    (hs : (∀ m ∈ s.msgs, m.msg = .inl false) ∧ (s.proc ()).out ≠ some true) :
    (∀ m ∈ t.msgs, m.msg = .inl false) ∧ (t.proc ()).out ≠ some true := by
  induction h with
  | refl => exact hs
  | @stepL s1 x s2 xl t htr _ ih =>
    apply ih
    cases x with
    | none => cases htr; exact hs
    | some m =>
      obtain ⟨hm, rfl⟩ := htr
      refine ⟨fun m' hm' => ?_, ?_⟩
      · simp only [Algorithm.recvMsg, flpI, add_zero] at hm'
        exact hs.1 m' (Multiset.mem_of_mem_erase hm')
      · have := hs.1 m hm
        simp only [Algorithm.recvMsg, flpI, ite_true, this]
        split
        · simp
        · exact hs.2

theorem trivRun : flpA.lts.OmegaExecution ⟨fun _ => flpA.start (fun _ => true)⟩ ⟨fun _ => none⟩ := fun _ => rfl

theorem faultyStart : ProcFaulty () (⟨fun _ => flpA.start (fun _ => true)⟩ : ωSequence (State Unit Unit Unit))
    ⟨fun _ => none⟩ :=
  ⟨0, ⟨m1, by simp [Algorithm.start, m1], rfl⟩, fun _ _ _ h => by simp at h⟩

theorem nPF1 : numProcFaulty (⟨fun _ => flpA.start (fun _ => true)⟩ : ωSequence (State Unit Unit Unit))
    ⟨fun _ => none⟩ = 1 := by
  have : {p : Unit | ProcFaulty p (⟨fun _ => flpA.start (fun _ => true)⟩ : ωSequence (State Unit Unit Unit))
    ⟨fun _ => none⟩} = Set.univ := Set.eq_univ_of_forall (fun _ => faultyStart)
  simp [numProcFaulty, this]


theorem fsa0 {P M S : Type} [DecidableEq P] [DecidableEq M] (a : Algorithm P M S) (d : DeliverMsg P M S)
    (ps : Set P) (s0 : State P M S) : a.fairSegActions d ps s0 0 = (d.scheduleMsgs ps s0).1 := by
  have := FairScheduler.fairScheduler_step (a := a) (d := d) ps s0 0
  rw [FairScheduler.fairScheduler_init] at this
  rw [this]

theorem sch1 (d : DeliverMsg Unit Unit Unit) : d.scheduleMsgs Set.univ flpS1 = d.foldList flpS1 [m1] ∅ := by
  simp [DeliverMsg.scheduleMsgs, flpS1]

theorem sch0 (d : DeliverMsg Unit Unit Unit) (ps : Set Unit) : d.scheduleMsgs ps flpS0 = ([none], flpS0) := by
  simp [DeliverMsg.scheduleMsgs, flpS0]

def dS : DeliverMsg Unit Unit Unit := fun s m => ([some m], s)
def dE : DeliverMsg Unit Unit Unit := fun s _ => ([], s)

theorem fl1S : (dS.foldList flpS1 [m1] ∅).1 = [some m1] := by simp [DeliverMsg.foldList, dS]
theorem fl1E : (dE.foldList flpS1 [m1] ∅).1 = [] := by simp [DeliverMsg.foldList, dE]

theorem segz (f : ℕ → ℕ) : Nat.segment f 0 = 0 := by
  unfold Nat.segment
  rw [Nat.count_succ, Nat.count_zero]
  split <;> rfl

theorem flat0 {α : Type} [Inhabited α] (ls : ωSequence (List α)) : ls.flatten 0 = (ls 0)[0]! := by
  rw [ωSequence.flatten_def, segz]; rfl

theorem getForall {α : Type*} {r : Option α → Prop} {l : List (Option α)} (hf : l.Forall r) (hn : r none) (i : ℕ) :
    r l[i]! := by
  rw [List.getElem!_eq_getElem?_getD]
  cases h : l[i]? with
  | none => exact hn
  | some x => exact List.forall_iff_forall_mem.mp hf x (List.mem_of_getElem? h)


theorem cumLen1 {α : Type} (ls : ωSequence (List α)) (h : ∀ k, (ls k).length = 1) (k : ℕ) : ls.cumLen k = k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [ωSequence.cumLen_succ, ih, h]

theorem crvStay {P : Type*} {M : Type*} {S : Type*} [DecidableEq P] [DecidableEq M] (a : Algorithm P M S)
    {s t : State P M S} (h : a.CanReachVia ∅ s t) : t = s := by
  induction h with
  | refl => rfl
  | tail _ hst ih =>
    obtain ⟨x, hx, ht⟩ := hst
    subst ih
    cases x with
    | none => exact ht
    | some m => exact absurd hx (by simp [DestIn])

-- no algorithm on at most one process is 1-pseudo-consensus: with ps = ∅ the start state must be decided
theorem noPC1 {P : Type*} {M : Type*} {S : Type*} [DecidableEq P] [DecidableEq M] [Fintype P]
    (a : Algorithm P M S) (hc : Fintype.card P ≤ 1) : ¬ a.PseudoConsensus 1 := by
  rintro ⟨-, ht⟩
  obtain ⟨s', b, hcrv, p, hp⟩ := ht (fun _ => true) _ Algorithm.reachable_start ∅ (by simp; omega)
  rw [crvStay a hcrv] at hp
  simp [Algorithm.start, State.ProcDecided] at hp

-- never-deciding algorithms reach no decided state from the start
theorem noDecStart {P M S : Type} [DecidableEq P] [DecidableEq M] [Fintype P] {a : Algorithm P M S}
    (hout : ∀ m q, a.out m q = none) {inp : P → Bool} {s : State P M S} (h : a.lts.CanReach (a.start inp) s)
    {b : Bool} : ¬ s.Decided b := by
  rintro ⟨p, hp⟩
  obtain ⟨xl, h⟩ := h
  have := noOut hout h (fun _ => rfl) p
  rw [State.ProcDecided] at hp
  rw [hp] at this; cases this

def flpAB : Algorithm Bool Unit Unit := ⟨fun _ => (), fun _ _ => (), fun _ _ => 0, fun _ _ => none⟩

def flpD : Algorithm Bool Unit Unit :=
  ⟨fun _ => (), fun _ _ => (), fun _ _ => 0, fun m _ => match m.msg with | .inl b => some b | .inr _ => none⟩
def flpC (c : Bool) : Algorithm Bool Unit Unit := ⟨fun _ => (), fun _ _ => (), fun _ _ => 0, fun _ _ => some c⟩
def flpT : Algorithm Unit Unit Unit := ⟨fun _ => (), fun _ _ => (), fun _ _ => 0, fun _ _ => some true⟩

-- flpD: state after process true received its input `true` (inputs id)
def sD : State Bool Unit Unit := flpD.recvMsg ⟨true, .inl true⟩ (flpD.start id)

theorem sD_reach : flpD.Reachable id sD := ⟨[some ⟨true, .inl true⟩], .single _ ⟨by decide, rfl⟩⟩
theorem sD_dec : sD.Decided true := ⟨true, by simp [sD, Algorithm.recvMsg, Algorithm.start, flpD, State.ProcDecided]⟩
theorem sD_cdw : flpD.CanDecideWithout sD true false :=
  ⟨flpD.recvMsg ⟨false, .inl false⟩ sD, .single ⟨some ⟨false, .inl false⟩, by simp [DestIn], by decide, rfl⟩,
    ⟨false, by simp [sD, Algorithm.recvMsg, Algorithm.start, flpD, State.ProcDecided]⟩⟩

-- the constant-c algorithm: process false decides c on its input message
theorem cdwC (c : Bool) (inp : Bool → Bool) : (flpC c).CanDecideWithout ((flpC c).start inp) true c :=
  ⟨(flpC c).recvMsg ⟨false, .inl (inp false)⟩ ((flpC c).start inp),
    .single ⟨some ⟨false, .inl (inp false)⟩, by simp [DestIn], by simp [Algorithm.start], rfl⟩,
    ⟨false, by simp [Algorithm.recvMsg, Algorithm.start, flpC, State.ProcDecided]⟩⟩

theorem flatNone {α : Type} (ls : ωSequence (List (Option α))) (h : ∀ k, ls k = [none]) (j : ℕ) :
    ls.flatten j = none := by
  rw [ωSequence.flatten_def, h]
  exact getForall (r := (· = none)) (by simp) rfl _


-- flpP: process true, on its input, poisons process false; process false decides true on an input
-- message unless poisoned; nobody ever decides false
def flpP : Algorithm Bool Unit Bool where
  init _ := false
  next m q := match m.msg with | .inr _ => true | .inl _ => q.state
  send m _ := if m.dest = true then {⟨false, .inr ()⟩} else 0
  out m q := if m.dest = false then (match m.msg with | .inl _ => if q.state then none else some true | .inr _ => none)
    else none

theorem outP (m : Message Bool Unit) (q : ProcState Bool) : flpP.out m q ≠ some false := by
  rcases m with ⟨d, msg | msg⟩ <;> cases d <;> simp only [flpP] <;> split_ifs <;> simp

theorem Pinv {t u : State Bool Unit Bool} {xl : List (Action Bool Unit)} (h : flpP.lts.MTr t xl u)
    (ht : ∀ q, (t.proc q).out ≠ some false) : ∀ q, (u.proc q).out ≠ some false := by
  induction h with
  | refl => exact ht
  | @stepL s1 x s2 xl s3 htr _ ih =>
    apply ih
    cases x with
    | none => cases htr; exact ht
    | some m =>
      obtain ⟨-, rfl⟩ := htr
      intro q
      simp only [Algorithm.recvMsg]
      split
      · split
        · exact outP _ _
        · exact ht _
      · exact ht q

def PJ (t : State Bool Unit Bool) : Prop :=
  (t.proc false).state = true ∧ (t.proc false).out = none ∧ (t.proc true).out = none

theorem Pinv2 {t u : State Bool Unit Bool} (h : flpP.CanReachVia {true}ᶜ t u) (ht : PJ t) : PJ u := by
  induction h with
  | refl => exact ht
  | tail _ hst ih =>
    obtain ⟨x, hx, htr⟩ := hst
    cases x with
    | none => cases htr; exact ih
    | some m' =>
      obtain ⟨-, rfl⟩ := htr
      obtain ⟨d, msg⟩ := m'
      have hd : d = false := by simpa [DestIn] using hx
      subst hd
      obtain ⟨h1, h2, h3⟩ := ih
      cases msg <;> simp [PJ, Algorithm.recvMsg, flpP, h1, h2, h3]

def sP : State Bool Unit Bool := flpP.recvMsg ⟨true, .inl true⟩ (flpP.start fun _ => true)

-- flpN lemmas (Probe1)
def flpN : Algorithm Bool Unit Unit where
  init _ := ()
  next _ _ := ()
  send m _ := if m.dest = true then (match m.msg with | .inl b => {⟨false, .inl b⟩} | .inr _ => 0) else 0
  out m _ := if m.dest = false then (match m.msg with | .inl b => some b | .inr _ => none) else none

theorem flpN_tr_true {t u : State Bool Unit Unit} {x : Action Bool Unit} (h : flpN.lts.Tr t x u)
    (ht : (t.proc true).out = none) : (u.proc true).out = none := by
  cases x with
  | none => cases h; exact ht
  | some m =>
    obtain ⟨-, rfl⟩ := h
    rcases m with ⟨d, msg⟩
    cases d <;> simp_all [Algorithm.recvMsg, flpN]

theorem flpN_mtr_true {t u : State Bool Unit Unit} {μs : List (Action Bool Unit)}
    (h : flpN.lts.MTr t μs u) (ht : (t.proc true).out = none) : (u.proc true).out = none := by
  induction h with
  | refl => exact ht
  | stepL htr _ ih => exact ih (flpN_tr_true htr ht)

-- receiving an input-tagged message at process false makes it decide
theorem nRecv (s1 : State Bool Unit Unit) (c : Bool) :
    ∃ b, ((flpN.recvMsg ⟨false, .inl c⟩ s1).proc false).out = some b := by
  simp only [Algorithm.recvMsg, flpN, ite_true]
  cases (s1.proc false).out <;> simp

theorem nA {t u : State Bool Unit Unit} {xl : List (Action Bool Unit)} (h : flpN.lts.MTr t xl u) {c : Bool}
    (hm : some (⟨false, .inl c⟩ : Message Bool Unit) ∈ xl) : ∃ b, (u.proc false).out = some b := by
  induction h with
  | refl => simp at hm
  | @stepL s1 x s2 xl s3 htr hrest ih =>
    rcases List.mem_cons.mp hm with e | hm'
    · subst e
      obtain ⟨-, rfl⟩ := htr
      obtain ⟨b, hb⟩ := nRecv s1 c
      exact ⟨b, Algorithm.procDecided_stable (a := flpN) (p := false) (b := b) hb ⟨xl, hrest⟩⟩
    · exact ih hm'

theorem flpN_uni {t : State Bool Unit Unit} {c : Bool} (ht : (t.proc true).out = none)
    (hf : (t.proc false).out = some c) : ¬ flpN.NonUniform t := by
  intro hn
  have key : ∀ b, b = c := by
    intro b
    obtain ⟨p, u, hu, q, hq⟩ := hn b
    obtain ⟨xl, hx⟩ := CanReachVia.canReach hu
    have ht' := flpN_mtr_true hx ht
    have hf' := Algorithm.procDecided_stable (a := flpN) (p := false) (b := c) hf ⟨xl, hx⟩
    cases q
    · have : (u.proc false).out = some b := hq
      rw [hf'] at this; exact (Option.some.inj this).symm
    · have : (u.proc true).out = some b := hq
      rw [ht'] at this; cases this
  exact absurd ((key true).trans (key false).symm) (by decide)

-- the reachable non-uniform state of Probe1's nus8: process true has forwarded its input
def sN : State Bool Unit Unit := flpN.recvMsg ⟨true, .inl true⟩ (flpN.start id)
theorem sN_mem (b : Bool) : (⟨false, .inl b⟩ : Message Bool Unit) ∈ sN.msgs := by cases b <;> decide
theorem sN_true : (sN.proc true).out = none := by simp [sN, Algorithm.recvMsg, Algorithm.start, flpN]
theorem sN_false : (sN.proc false).out = none := by simp [sN, Algorithm.recvMsg, Algorithm.start]
theorem sN_reach : flpN.Reachable id sN := ⟨[some ⟨true, .inl true⟩], .single _ ⟨by decide, rfl⟩⟩
theorem sN_nu : flpN.NonUniform sN := fun b => ⟨true, flpN.recvMsg ⟨false, .inl b⟩ sN,
    .single ⟨some ⟨false, .inl b⟩, by simp [DestIn], sN_mem b, rfl⟩,
    ⟨false, by simp [Algorithm.recvMsg, sN_false, flpN, State.ProcDecided]⟩⟩

end W2c3

section FLPV
open W2c3 Cslib Cslib.FLP


-- `Cslib.FLP.Message.ext` idx 4: necessary (different destinations)
theorem mext4 : ¬ drop0% Cslib.FLP.Message.ext 4 := fun h =>
  absurd (@h Bool Unit ⟨true, .inl true⟩ ⟨false, .inl true⟩ rfl) (by decide)

-- `Cslib.FLP.Message.ext` idx 5: necessary (different contents)
theorem mext5 : ¬ drop0% Cslib.FLP.Message.ext 5 := fun h =>
  absurd (@h Bool Unit ⟨true, .inl true⟩ ⟨true, .inl false⟩ rfl) (by decide)

-- `Cslib.FLP.Algorithm.tr_none` idx 8: necessary
theorem trn8 : ¬ drop0% Cslib.FLP.Algorithm.tr_none 8 := fun h => by
  have := congrArg State.msgs (@h Unit Unit Unit _ _ flpA flpS0 flpS1)
  simp [flpS0, flpS1] at this

-- `Cslib.FLP.Algorithm.reachable_stable` idx 10: necessary (decided state, never reachable for flpA)
theorem rst10 : ¬ drop0% Cslib.FLP.Algorithm.reachable_stable 10 := fun h => by
  have := flpA_noDecS (@h Unit Unit Unit _ _ flpA (fun _ => true) _ flpSd flpSd (LTS.CanReach.refl _ _))
  simp [flpSd] at this

-- `Cslib.FLP.Algorithm.reachable_stable` idx 11: necessary
theorem rst11 : ¬ drop0% Cslib.FLP.Algorithm.reachable_stable 11 := fun h => by
  have := flpA_noDecS (@h Unit Unit Unit _ _ flpA (fun _ => true) _ _ flpSd Algorithm.reachable_start)
  simp [flpSd] at this

-- `Cslib.FLP.Algorithm.procDecided_stable` idx 10: necessary
theorem pds10 : ¬ drop0% Cslib.FLP.Algorithm.procDecided_stable 10 := fun h => by
  have := @h Unit Unit Unit _ _ flpA flpS0 flpS0 () true (LTS.CanReach.refl _ _)
  simp [flpS0, State.ProcDecided] at this

-- `Cslib.FLP.Algorithm.procDecided_stable` idx 11: necessary
theorem pds11 : ¬ drop0% Cslib.FLP.Algorithm.procDecided_stable 11 := fun h => by
  have := @h Unit Unit Unit _ _ flpA flpSd flpS0 () true rfl
  simp [flpS0, State.ProcDecided] at this

-- `Cslib.FLP.Algorithm.decided_stable` idx 9: necessary
theorem ds9 : ¬ drop0% Cslib.FLP.Algorithm.decided_stable 9 := fun h => by
  obtain ⟨p, hp⟩ := @h Unit Unit Unit _ _ flpA flpS0 flpS0 true (LTS.CanReach.refl _ _)
  simp [flpS0, State.ProcDecided] at hp

-- `Cslib.FLP.Algorithm.decided_stable` idx 10: necessary
theorem ds10 : ¬ drop0% Cslib.FLP.Algorithm.decided_stable 10 := fun h => by
  obtain ⟨p, hp⟩ := @h Unit Unit Unit _ _ flpA flpSd flpS0 true ⟨(), rfl⟩
  simp [flpS0, State.ProcDecided] at hp

-- `Cslib.FLP.Algorithm.recvMsg_comm` idx 9: necessary (m1 = m2, received once)
theorem rmc9 : ¬ drop0% Cslib.FLP.Algorithm.recvMsg_comm 9 := fun h => by
  have := (@h Unit Unit Unit _ _ flpA m1 m1 flpS1 (by simp [flpS1]) (by simp [flpS1])).1
  rw [rA] at this
  simp [flpS0, State.ProcDecided] at this


-- `Cslib.FLP.Algorithm.recvMsg_comm` idx 10: necessary (m1 not in flight)
theorem rmc10 : ¬ drop0% Cslib.FLP.Algorithm.recvMsg_comm 10 := fun h => by
  have := (@h Bool Unit Unit _ _ flpAB ⟨false, .inl true⟩ ⟨true, .inl true⟩ ⟨{⟨true, .inl true⟩}, fun _ => ⟨(), none⟩⟩
    (by decide) (by simp)).2.1
  simp [Algorithm.recvMsg, flpAB] at this

-- `Cslib.FLP.Algorithm.recvMsg_comm` idx 11: necessary (m2 not in flight)
theorem rmc11 : ¬ drop0% Cslib.FLP.Algorithm.recvMsg_comm 11 := fun h => by
  have := (@h Bool Unit Unit _ _ flpAB ⟨false, .inl true⟩ ⟨true, .inl true⟩ ⟨{⟨false, .inl true⟩}, fun _ => ⟨(), none⟩⟩
    (by decide) (by simp)).1
  simp [Algorithm.recvMsg, flpAB] at this

-- `Cslib.FLP.Algorithm.tr_diamond` idx 12: necessary (the same message on both sides, ps = ∅)
theorem trd12 : ¬ drop0% Cslib.FLP.Algorithm.tr_diamond 12 := fun h => by
  obtain ⟨s', h1, -⟩ := @h Unit Unit Unit _ _ flpA ∅ (some m1) (some m1) flpS1 flpS0 flpS0 trA (by simp [DestIn]) trA
  exact absurd h1.1 (by simp [flpS0])

-- `Cslib.FLP.Algorithm.tr_diamond` idx 13: necessary
theorem trd13 : ¬ drop0% Cslib.FLP.Algorithm.tr_diamond 13 := fun h => by
  obtain ⟨s', -, h2⟩ := @h Unit Unit Unit _ _ flpA Set.univ (some m1) none flpS0 flpS0 flpS0 (by simp [DestIn])
    trivial rfl
  exact absurd h2.1 (by simp [flpS0])

-- `Cslib.FLP.Algorithm.tr_diamond` idx 14: necessary
theorem trd14 : ¬ drop0% Cslib.FLP.Algorithm.tr_diamond 14 := fun h => by
  obtain ⟨s', h1, -⟩ := @h Unit Unit Unit _ _ flpA Set.univ (some m1) (some m1) flpS1 flpS0 flpS0 (by simp [DestIn]) trA trA
  exact absurd h1.1 (by simp [flpS0])

-- `Cslib.FLP.Algorithm.mTr_notRcvd_enabled` idx 10: necessary
theorem mne10 : ¬ drop0% Cslib.FLP.Algorithm.mTr_notRcvd_enabled 10 := fun h => by
  have := @h Unit Unit Unit _ _ flpA flpS1 flpS0 [] m1 (by simp [flpS1]) (by simp)
  simp [flpS0, State.ProcDecided] at this

-- `Cslib.FLP.Algorithm.mTr_notRcvd_enabled` idx 12: necessary
theorem mne12 : ¬ drop0% Cslib.FLP.Algorithm.mTr_notRcvd_enabled 12 := fun h => by
  have := @h Unit Unit Unit _ _ flpA flpS1 flpS0 [some m1] m1 (.single _ trA) (by simp [flpS1])
  simp [flpS0, State.ProcDecided] at this

-- `Cslib.FLP.Algorithm.omega_notRcvd_enabled` idx 10: necessary (not an execution)
theorem one10 : ¬ drop0% Cslib.FLP.Algorithm.omega_notRcvd_enabled 10 := fun h => by
  have := @h Unit Unit Unit _ _ flpA (sqS flpS1 flpS0) ⟨fun _ => none⟩ 0 m1 (by simp [sqS, sqA, flpS1]) (by simp) 1 (by omega)
  simp [sqS, sqA, flpS0] at this

-- `Cslib.FLP.Algorithm.omega_notRcvd_enabled` idx 11: necessary
theorem one11 : ¬ drop0% Cslib.FLP.Algorithm.omega_notRcvd_enabled 11 := fun h => by
  have := @h Unit Unit Unit _ _ flpA ⟨fun _ => flpS0⟩ ⟨fun _ => none⟩ 0 m1 (fun _ => rfl) (by simp) 0 le_rfl
  simp [flpS0, State.ProcDecided] at this

-- `Cslib.FLP.Algorithm.omega_notRcvd_enabled` idx 12: necessary
theorem one12 : ¬ drop0% Cslib.FLP.Algorithm.omega_notRcvd_enabled 12 := fun h => by
  have := @h Unit Unit Unit _ _ flpA (sqS flpS1 flpS0) (sqA (some m1) none) 0 m1
    (fun n => by rcases n with _ | n; exact trA; rfl) (by simp [sqS, sqA, flpS1]) 1 (by omega)
  simp [sqS, sqA, flpS0] at this

def flpF : Algorithm Unit Unit Unit :=
  ⟨fun _ => (), fun _ _ => (), fun m _ => match m.msg with | .inl _ => {⟨(), .inr ()⟩} | .inr _ => 0, fun _ _ => none⟩

-- `Cslib.FLP.Algorithm.omega_notRcvd_enabled` idx 14: necessary (the message is sent at step 0)
theorem one14 : ¬ drop0% Cslib.FLP.Algorithm.omega_notRcvd_enabled 14 := fun h => by
  have := @h Unit Unit Unit _ _ flpF (sqS flpS1 (flpF.recvMsg m1 flpS1)) (sqA (some m1) none) 1 ⟨(), .inr ()⟩
    (fun n => by rcases n with _ | n; exact ⟨by simp [sqS, flpS1], rfl⟩; rfl)
    (by simp [sqS, sqA, Algorithm.recvMsg, flpF, m1]) (fun j hj => by simp [sqA]; omega) 0
  simp [sqS, sqA, flpS1, m1] at this


-- `Cslib.FLP.CanReachVia.canReach` idx 9: necessary (decided state cannot reach an undecided one)
theorem crvc9 : ¬ drop0% Cslib.FLP.CanReachVia.canReach 9 := fun h => by
  have := Algorithm.procDecided_stable (b := true) (p := ()) (show flpSd.ProcDecided () true from rfl)
    (@h Unit Unit Unit _ _ flpA ∅ flpSd flpS0)
  simp [flpS0, State.ProcDecided] at this

-- `Cslib.FLP.CanReachVia.stepL` idx 11: necessary (ps = ∅, a real message step)
theorem crvs11 : ¬ drop0% Cslib.FLP.CanReachVia.stepL 11 := fun h => by
  have := flpCrvStay flpA (fun p hp => hp) (@h Unit Unit Unit _ _ flpA ∅ (some m1) flpS1 flpS0 flpS0 trA .refl)
  have := congrArg State.msgs this
  simp [flpS0, flpS1] at this

-- `Cslib.FLP.CanReachVia.stepL` idx 12: necessary (no step from flpS0 to flpS1)
theorem crvs12 : ¬ drop0% Cslib.FLP.CanReachVia.stepL 12 := fun h => by
  have := flpCrvStay flpA (fun p hp => hp) (@h Unit Unit Unit _ _ flpA ∅ none flpS0 flpS1 flpS1 trivial .refl)
  have := congrArg State.msgs this
  simp [flpS0, flpS1] at this

-- `Cslib.FLP.CanReachVia.diamond` idx 10: necessary
theorem crvd10 : ¬ drop0% Cslib.FLP.CanReachVia.diamond 10 := fun h => by
  obtain ⟨s', h1, h2⟩ := @h Unit Unit Unit _ _ flpA Set.univ flpSd flpS0 flpSd .refl
  rw [flpCrvStay flpA (by simp) h1] at h2
  have := Algorithm.procDecided_stable (b := true) (p := ()) (show flpSd.ProcDecided () true from rfl)
    (CanReachVia.canReach h2)
  simp [flpS0, State.ProcDecided] at this

-- `Cslib.FLP.CanReachVia.diamond` idx 11: necessary
theorem crvd11 : ¬ drop0% Cslib.FLP.CanReachVia.diamond 11 := fun h => by
  obtain ⟨s', h1, h2⟩ := @h Unit Unit Unit _ _ flpA ∅ flpS0 flpS0 flpSd .refl
  rw [flpCrvStay flpA (by simp) h2] at h1
  have := flpA_noDec (CanReachVia.canReach h1)
  simp [flpSd] at this

-- `Cslib.FLP.CanReachVia.subset_inp` idx 11: necessary (flpI decides its input; inputs differ)
theorem crvsi11 : ¬ drop0% Cslib.FLP.CanReachVia.subset_inp 11 := fun h => by
  obtain ⟨s2, h2, hp⟩ := @h Unit Unit Unit _ _ flpI _ Set.univ (fun _ => true) (fun _ => false)
    (flpI.recvMsg ⟨(), .inl true⟩ (flpI.start fun _ => true))
    (.single ⟨some ⟨(), .inl true⟩, trivial, by simp [Algorithm.start], rfl⟩)
  obtain ⟨xl, hx⟩ := CanReachVia.canReach h2
  have := (flpI_inv hx ⟨by simp [Algorithm.start], by simp [Algorithm.start]⟩).2
  rw [hp] at this
  simp [Algorithm.recvMsg, flpI, Algorithm.start] at this

-- `Cslib.FLP.CanReachVia.subset_inp` idx 12: necessary (ps = ∅, decided target)
theorem crvsi12 : ¬ drop0% Cslib.FLP.CanReachVia.subset_inp 12 := fun h => by
  obtain ⟨s2, h2, hp⟩ := @h Unit Unit Unit _ _ flpA _ ∅ (fun _ => true) (fun _ => true) flpSd (fun _ h => h.elim)
  rw [flpCrvStay flpA (by simp) h2] at hp
  have := congrFun hp ()
  simp [Algorithm.start, flpSd] at this

-- `Cslib.FLP.not_procFaulty_of_numProcFaulty` idx 6: necessary (no processes)
theorem npf6 : ¬ drop0% Cslib.FLP.not_procFaulty_of_numProcFaulty 6 := fun h => by
  obtain ⟨p, -⟩ := @h Empty Unit Unit _ ⟨fun _ => ⟨0, fun p => p.elim⟩⟩ ⟨fun _ => none⟩
  exact p.elim

-- `Cslib.FLP.numProcFaulty_le_not_procFair` idx 7: necessary (the only process is faulty, ps = univ)
theorem npfl7 : ¬ drop0% Cslib.FLP.numProcFaulty_le_not_procFair 7 := fun h => by
  have := @h Unit Unit Unit _ ⟨fun _ => flpA.start (fun _ => true)⟩ ⟨fun _ => none⟩ Set.univ
  rw [nPF1] at this
  simp at this

-- `Cslib.FLP.AdmissibleRun.fault_mono` idx 12: necessary (one faulty process, f' = 0)
theorem arfm12 : ¬ drop0% Cslib.FLP.AdmissibleRun.fault_mono 12 := fun h => by
  have := (@h Unit Unit Unit _ _ flpA (fun _ => true) _ 1 0 ⟨fun _ => none⟩ ⟨fun _ => flpA.start (fun _ => true)⟩
    ⟨rfl, trivRun, fun _ => .inl faultyStart, nPF1.le⟩).2.2.2
  rw [nPF1] at this
  simp at this

-- `Cslib.FLP.AdmissibleRun.fault_mono` idx 13: necessary (run not starting at the start state)
theorem arfm13 : ¬ drop0% Cslib.FLP.AdmissibleRun.fault_mono 13 := fun h => by
  have := congrArg (fun s => (State.proc s ()).out)
    (@h Unit Unit Unit _ _ flpA (fun _ => true) _ 0 0 ⟨fun _ => none⟩ ⟨fun _ => flpSd⟩ le_rfl).1
  simp [flpSd, Algorithm.start] at this

-- `Cslib.FLP.Consensus.fault_mono` idx 9: necessary (a 0-consensus algorithm on 2 processes is not 1-tolerant)
theorem cfm9 : ¬ drop0% Cslib.FLP.Consensus.fault_mono 9 := fun h =>
  Consensus.one_not_exists (P := Fin 2) (M := Bool) (S := Unit) (by simp)
    ⟨_, @h (Fin 2) Bool Unit _ _ _ _ 0 1 (Cslib.FLP.ZeroFaultAlg.consensus_zero (n := 2) (by decide))⟩

-- `Cslib.FLP.Algorithm.not_fair_stay_enabled` idx 9: necessary (message disappears without a step)
theorem nfse9 : ¬ drop0% Cslib.FLP.Algorithm.not_fair_stay_enabled 9 := fun h => by
  obtain ⟨m, -, k, -, hk⟩ := @h Unit Unit Unit _ _ flpA (sqS flpS1 flpS0) ⟨fun _ => none⟩ ()
    (fun hf => by obtain ⟨j, -, hj⟩ := hf m1 rfl 0 (by simp [sqS, flpS1]); simp at hj)
  have := (hk (k + 1) (by omega)).1
  simp [sqS, flpS0] at this

-- `Cslib.FLP.Algorithm.not_fair_stay_enabled` idx 10: necessary (no messages at all)
theorem nfse10 : ¬ drop0% Cslib.FLP.Algorithm.not_fair_stay_enabled 10 := fun h => by
  obtain ⟨m, -, k, hk, -⟩ := @h Unit Unit Unit _ _ flpA ⟨fun _ => flpS0⟩ ⟨fun _ => none⟩ () (fun _ => rfl)
  simp [flpS0] at hk

-- `Cslib.FLP.Algorithm.drop_procFair_iff` idx 8: necessary (unfair at step 0 only)
theorem dpf8 : ¬ drop0% Cslib.FLP.Algorithm.drop_procFair_iff 8 := fun h => by
  have := (@h Unit Unit Unit _ _ flpA (sqS flpS1 flpS0) ⟨fun _ => none⟩ () 1).1
    (fun m _ k hk => by simp [ωSequence.get_drop, sqS, flpS0] at hk)
  obtain ⟨j, -, hj⟩ := this m1 rfl 0 (by simp [sqS, flpS1])
  simp at hj


-- `Cslib.FLP.DeliverMsg.foldList_forallActions` idx 10: necessary (r = False, d delivers the message)
theorem flfa10 : ¬ drop0% Cslib.FLP.DeliverMsg.foldList_forallActions 10 := fun h => by
  have := @h Unit Unit Unit _ _ dS (fun _ => False) flpS1 [m1] ∅
  rw [fl1S] at this
  simp at this

-- `Cslib.FLP.FairScheduler.fairSeg_forallActions` idx 11: necessary (r = (· = none), d delivers)
theorem fsfa11 : ¬ drop0% Cslib.FLP.FairScheduler.fairSeg_forallActions 11 := fun h => by
  have := @h Unit Unit Unit _ _ flpA dS (· = none) Set.univ flpS1 0 rfl
  rw [fsa0, sch1, fl1S] at this
  simp at this

-- `Cslib.FLP.FairScheduler.fairSeg_forallActions` idx 12: necessary (r = (· ≠ none), stutter step)
theorem fsfa12 : ¬ drop0% Cslib.FLP.FairScheduler.fairSeg_forallActions 12 := fun h => by
  have := @h Unit Unit Unit _ _ flpA dS (· ≠ none) Set.univ flpS0 0 (fun _ _ => by simp [dS])
  rw [fsa0, sch0] at this
  simp at this

-- `Cslib.FLP.FairScheduler.fairDeliverMsg_foldList` idx 9: necessary (d delivers nothing)
theorem fdmf9 : ¬ drop0% Cslib.FLP.FairScheduler.fairDeliverMsg_foldList 9 := fun h => by
  have := (@h Unit Unit Unit _ _ flpA dE Set.univ (fun _ => True) flpS1 [m1] ∅
    ⟨trivial, fun m hm _ => by simp at hm; subst hm; simp [flpS1]⟩)
  have e : (dE.foldList flpS1 [m1] ∅) = ([], flpS1) := by simp [DeliverMsg.foldList, dE]
  rw [e] at this
  exact absurd (this.2.2 m1 (by simp) (by simp)) (by simp)

-- `Cslib.FLP.FairScheduler.fairDeliverMsg_foldList` idx 13: necessary (q = False, so d is vacuously fair)
theorem fdmf13 : ¬ drop0% Cslib.FLP.FairScheduler.fairDeliverMsg_foldList 13 := fun h => by
  have := (@h Unit Unit Unit _ _ flpA dE Set.univ (fun _ => False) (fun _ _ h => h.2.2.elim) flpS1 [] ∅)
  simp [DeliverMsg.foldList] at this

-- `Cslib.FLP.FairScheduler.fairDeliverMsg_scheduleMsgs` idx 9: necessary (d delivers nothing)
theorem fdms9 : ¬ drop0% Cslib.FLP.FairScheduler.fairDeliverMsg_scheduleMsgs 9 := fun h => by
  have := (@h Unit Unit Unit _ _ flpA dE Set.univ (fun _ => True) flpS1 trivial).2.2.1
  rw [sch1, fl1E] at this
  simp at this

-- `Cslib.FLP.FairScheduler.fairDeliverMsg_scheduleMsgs` idx 11: necessary (q = False)
theorem fdms11 : ¬ drop0% Cslib.FLP.FairScheduler.fairDeliverMsg_scheduleMsgs 11 := fun h =>
  (@h Unit Unit Unit _ _ flpA dE Set.univ (fun _ => False) (fun _ _ h => h.2.2.elim) flpS1).1

-- `Cslib.FLP.FairScheduler.fair_fairSegs` idx 9: necessary (d delivers nothing: empty first segment)
theorem ffs9 : ¬ drop0% Cslib.FLP.FairScheduler.fair_fairSegs 9 := fun h => by
  have := (@h Unit Unit Unit _ _ flpA dE Set.univ (fun _ => True) flpS1 trivial 0).2.2.1
  rw [fsa0, sch1, fl1E] at this
  simp at this

-- `Cslib.FLP.FairScheduler.fair_fairSegs` idx 11: necessary (q = False)
theorem ffs11 : ¬ drop0% Cslib.FLP.FairScheduler.fair_fairSegs 11 := fun h =>
  (@h Unit Unit Unit _ _ flpA dE Set.univ (fun _ => False) (fun _ _ h => h.2.2.elim) flpS1 0).1

-- `Cslib.FLP.FairScheduler.fair_omegaExecution` idx 9: necessary (empty first segment)
theorem foe9 : ¬ drop0% Cslib.FLP.FairScheduler.fair_omegaExecution 9 := fun h => by
  obtain ⟨ss, -, -, -, -, hpos, -⟩ := @h Unit Unit Unit _ _ flpA dE Set.univ (fun _ => True) flpS1 trivial
  have := hpos 0
  rw [fsa0, sch1, fl1E] at this
  simp at this

-- `Cslib.FLP.FairScheduler.fair_omegaExecution` idx 11: necessary (q = False)
theorem foe11 : ¬ drop0% Cslib.FLP.FairScheduler.fair_omegaExecution 11 := fun h => by
  obtain ⟨ss, -, -, -, hq, -⟩ := @h Unit Unit Unit _ _ flpA dE Set.univ (fun _ => False) (fun _ _ h => h.2.2.elim) flpS1
  exact hq 0

-- `Cslib.FLP.FairScheduler.omega_forall_actions` idx 10: removable (every flattened action is an action of some
-- segment, which satisfies r without fairness of d, or the default none)
theorem ofa10 : drop% Cslib.FLP.FairScheduler.omega_forall_actions 10 := by
  intro P M S _ _ a d ps q r s0 hs0 ha hn k
  rw [ωSequence.flatten_def]
  exact getForall (FairScheduler.fairSeg_forallActions ps s0 _ ha hn) hn _

-- `Cslib.FLP.FairScheduler.omega_forall_actions` idx 12: removable (same argument; q s0 is not used)
theorem ofa12 : drop% Cslib.FLP.FairScheduler.omega_forall_actions 12 := by
  intro P M S _ _ a d ps q r hd s0 ha hn k
  rw [ωSequence.flatten_def]
  exact getForall (FairScheduler.fairSeg_forallActions ps s0 _ ha hn) hn _

-- `Cslib.FLP.FairScheduler.omega_forall_actions` idx 13: necessary (r = (· = none), simpleDeliver delivers)
theorem ofa13 : ¬ drop0% Cslib.FLP.FairScheduler.omega_forall_actions 13 := fun h => by
  have := @h Unit Unit Unit _ _ flpA (flpA.simpleDeliver Set.univ) Set.univ (fun _ => True) (· = none)
    (PseudoConsensus.simpleDeliver_fair _) flpS1 trivial rfl 0
  rw [flat0, fsa0, sch1] at this
  simp [DeliverMsg.foldList, Algorithm.simpleDeliver, flpS1] at this

-- `Cslib.FLP.FairScheduler.omega_forall_actions` idx 14: necessary (r = (· ≠ none), stutter step first)
theorem ofa14 : ¬ drop0% Cslib.FLP.FairScheduler.omega_forall_actions 14 := fun h => by
  have := @h Unit Unit Unit _ _ flpA (flpA.simpleDeliver Set.univ) Set.univ (fun _ => True) (· ≠ none)
    (PseudoConsensus.simpleDeliver_fair _) flpS0 trivial
    (fun s m => by unfold Algorithm.simpleDeliver; split <;> simp) 0
  rw [flat0, fsa0, sch0] at this
  simp at this


-- `Cslib.FLP.FairScheduler.flatten_fairSegs` idx 9: necessary (segments not linked by executions)
theorem ffl9 : ¬ drop0% Cslib.FLP.FairScheduler.flatten_fairSegs 9 := fun h => by
  obtain ⟨ss, he, hts, -⟩ := @h Unit Unit Unit _ _ flpA ∅ (sqS flpS0 flpS1) ⟨fun _ => [none]⟩ (fun _ => by simp)
    (fun _ _ _ h => h.elim)
  have c1 := cumLen1 (⟨fun _ => [none]⟩ : ωSequence (List (Action Unit Unit))) (fun _ => rfl)
  have h0 := hts 0
  have h1 := hts 1
  rw [c1] at h0 h1
  have := he 0
  rw [flat0] at this
  change ss 1 = ss 0 at this
  rw [h0, h1] at this
  have := congrArg State.msgs this
  simp [sqS, flpS0, flpS1] at this

-- `Cslib.FLP.FairScheduler.flatten_fairSegs` idx 10: necessary (an empty first segment loses the first action)
theorem ffl10 : ¬ drop0% Cslib.FLP.FairScheduler.flatten_fairSegs 10 := fun h => by
  obtain ⟨ss, he, hts, -⟩ := @h Unit Unit Unit _ _ flpA ∅ ⟨fun n => if n ≤ 1 then flpS1 else flpS0⟩
    ⟨fun n => if n = 0 then [] else if n = 1 then [some m1] else [none]⟩
    (fun k => by
      rcases k with _ | _ | k
      · exact .refl
      · exact .single _ trA
      · exact .single _ (show flpS0 = flpS0 from rfl))
    (fun _ _ _ h => h.elim)
  have h0 : ss 0 = flpS1 := by simpa using hts 0
  have h2 : ss 1 = flpS0 := by simpa [ωSequence.cumLen_succ] using hts 2
  have e := he 0
  rw [flat0] at e
  change ss 1 = ss 0 at e
  rw [h0, h2] at e
  have := congrArg State.msgs e
  simp [flpS0, flpS1] at this

-- `Cslib.FLP.FairScheduler.flatten_fairSegs` idx 11: necessary (message never scheduled)
theorem ffl11 : ¬ drop0% Cslib.FLP.FairScheduler.flatten_fairSegs 11 := fun h => by
  obtain ⟨ss, -, hts, hf⟩ := @h Unit Unit Unit _ _ flpA Set.univ ⟨fun _ => flpS1⟩ ⟨fun _ => [none]⟩
    (fun _ => .single _ (show flpS1 = flpS1 from rfl)) (fun _ => by simp)
  have h0 := hts 0
  simp only [ωSequence.cumLen_zero] at h0
  obtain ⟨j, -, hj⟩ := hf () trivial m1 rfl 0 (by rw [h0]; simp [flpS1])
  rw [flatNone _ (fun _ => rfl)] at hj
  cases hj

-- `Cslib.FLP.OnePseudoConsensus.pseudoTermination` idx 8: necessary (flpA never decides)
theorem pt8 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.pseudoTermination 8 := fun h => by
  obtain ⟨s', b, hc, hd⟩ := @h Unit Unit Unit _ _ flpA (fun _ => true) _ _ Algorithm.reachable_start ()
  exact noDecStart (fun _ _ => rfl) (CanReachVia.canReach hc) hd

-- `Cslib.FLP.OnePseudoConsensus.canDecideWithout_exists` idx 8: necessary (flpA never decides)
theorem cdwe8 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.canDecideWithout_exists 8 := fun h => by
  obtain ⟨b, s', hc, hd⟩ := @h Unit Unit Unit _ _ flpA (fun _ => true) _ _ Algorithm.reachable_start ()
  exact noDecStart (fun _ _ => rfl) (CanReachVia.canReach hc) hd

-- `Cslib.FLP.OnePseudoConsensus.uniform_or_nonUniform` idx 8: necessary (flpA never decides)
theorem uon8 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.uniform_or_nonUniform 8 := fun h => by
  have key : ∀ b, ¬ flpA.CanDecideWithout (flpA.start fun _ => true) () b := fun b ⟨s', hc, hd⟩ =>
    noDecStart (fun _ _ => rfl) (CanReachVia.canReach hc) hd
  rcases @h Unit Unit Unit _ _ flpA (fun _ => true) _ _ Algorithm.reachable_start with h | h | h
  · exact key _ (h ()).1
  · exact key _ (h ()).1
  · obtain ⟨p, hp⟩ := h true; exact key _ hp

-- `Cslib.FLP.OnePseudoConsensus.decided_eq_canDecideWithout` idx 8: necessary (each process decides its input)
theorem dec8 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.decided_eq_canDecideWithout 8 := fun h =>
  absurd (@h Bool Unit Unit _ _ flpD id _ sD sD_reach true false true sD_dec sD_cdw) (by decide)

-- `Cslib.FLP.OnePseudoConsensus.decided_imp_uniform` idx 8: necessary (each process decides its input)
theorem diu8 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.decided_imp_uniform 8 := fun h =>
  ((@h Bool Unit Unit _ _ flpD id _ sD sD_reach true sD_dec) true).2 sD_cdw

-- `Cslib.FLP.OnePseudoConsensus.canDecideWithout_dest` idx 11: necessary (flpA never decides)
theorem cdwd11 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.canDecideWithout_dest 11 := fun h => by
  obtain ⟨s'', hr, p, hp⟩ := @h Unit Unit Unit _ _ flpA flpS1 flpS0 m1 true trA
  rw [flpCrvStay flpA (by simp) hr] at hp
  simp [flpS0, State.ProcDecided] at hp

-- `Cslib.FLP.OnePseudoConsensus.canDecideWithout_nondest` idx 10: necessary (s' unrelated decided state)
theorem cdwn10 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.canDecideWithout_nondest 10 := fun h => by
  obtain ⟨t, ht, hd⟩ := @h Bool Unit Unit _ _ flpAB ⟨0, fun _ => ⟨(), none⟩⟩ ⟨0, fun _ => ⟨(), some true⟩⟩
    ⟨false, .inl true⟩ true true (by decide) ⟨_, .refl, ⟨true, rfl⟩⟩
  obtain ⟨p, hp⟩ := hd
  obtain ⟨xl, hx⟩ := CanReachVia.canReach ht
  have := noOut (fun _ _ => rfl) hx (fun _ => rfl) p
  rw [State.ProcDecided] at hp
  rw [hp] at this; cases this

-- `Cslib.FLP.OnePseudoConsensus.canDecideWithout_nondest` idx 12: necessary (p = m.dest, flpT decides on m)
theorem cdwn12 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.canDecideWithout_nondest 12 := fun h => by
  obtain ⟨t, ht, p, hp⟩ := @h Unit Unit Unit _ _ flpT flpS1 (flpT.recvMsg m1 flpS1) m1 true
    ⟨by simp [flpS1], rfl⟩ () ⟨_, .refl, ⟨(), by simp [Algorithm.recvMsg, flpT, flpS1, State.ProcDecided]⟩⟩
  rw [flpCrvStay flpT (by simp) ht] at hp
  simp [flpS1, State.ProcDecided] at hp

-- `Cslib.FLP.OnePseudoConsensus.canDecideWithout_nondest` idx 13: necessary (flpAB never decides)
theorem cdwn13 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.canDecideWithout_nondest 13 := fun h => by
  obtain ⟨t, ht, p, hp⟩ := @h Bool Unit Unit _ _ flpAB ⟨{⟨false, .inl true⟩}, fun _ => ⟨(), none⟩⟩ _
    ⟨false, .inl true⟩ true ⟨by simp, rfl⟩ true (by decide)
  obtain ⟨xl, hx⟩ := CanReachVia.canReach ht
  have := noOut (fun _ _ => rfl) hx (fun _ => rfl) p
  rw [State.ProcDecided] at hp
  rw [hp] at this; cases this

-- `Cslib.FLP.OnePseudoConsensus.inpN_eqOn_except_singleton` idx 4: necessary (dependent; n = 0)
theorem ine4 : ¬ indep0% Cslib.FLP.OnePseudoConsensus.inpN_eqOn_except_singleton 4 := fun h =>
  absurd (@h Unit _ (Fintype.equivFin Unit) 0 (Nat.zero_le _)) (by decide)

-- `Cslib.FLP.OnePseudoConsensus.inpN_eqOn_except_singleton` idx 5: necessary (dependent; n = 2 > card Unit)
theorem ine5 : ¬ indep0% Cslib.FLP.OnePseudoConsensus.inpN_eqOn_except_singleton 5 := fun h =>
  absurd (@h Unit _ (Fintype.equivFin Unit) 2 (by decide)) (by simp)

-- `Cslib.FLP.OnePseudoConsensus.inpN_zero_no_true` idx 8: necessary (process false always decides true)
theorem inzt8 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.inpN_zero_no_true 8 := fun h =>
  @h Bool Unit Unit _ _ (flpC true) _ (Fintype.equivFin Bool) true (cdwC true _)

-- `Cslib.FLP.OnePseudoConsensus.inpN_zero_uniform` idx 8: necessary (process false always decides true)
theorem inzu8 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.inpN_zero_uniform 8 := fun h =>
  ((@h Bool Unit Unit _ _ (flpC true) _ (Fintype.equivFin Bool)) true).2 (cdwC true _)

-- `Cslib.FLP.OnePseudoConsensus.inpN_card_not_false` idx 8: necessary (process false always decides false)
theorem incf8 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.inpN_card_not_false 8 := fun h =>
  @h Bool Unit Unit _ _ (flpC false) _ (Fintype.equivFin Bool) true (cdwC false _)

-- `Cslib.FLP.OnePseudoConsensus.inpN_card_uniform` idx 8: necessary (process false always decides false)
theorem incu8 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.inpN_card_uniform 8 := fun h =>
  ((@h Bool Unit Unit _ _ (flpC false) _ (Fintype.equivFin Bool)) true).2 (cdwC false _)

-- `Cslib.FLP.OnePseudoConsensus.nonUniform_inp` idx 7: necessary (flpAB never decides)
theorem nui7 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.nonUniform_inp 7 := fun h => by
  obtain ⟨inp, hn⟩ := @h Bool Unit Unit _ _ flpAB _ (by simp)
  obtain ⟨p, s', hc, hd⟩ := hn true
  exact noDecStart (fun _ _ => rfl) (CanReachVia.canReach hc) hd

-- `Cslib.FLP.OnePseudoConsensus.nonUniform_inp` idx 8: removable (for card P ≤ 1 there is no 1-pseudo-consensus
-- algorithm: with ps = ∅ the start state would have to be decided)
theorem nui8 : drop% Cslib.FLP.OnePseudoConsensus.nonUniform_inp 8 := by
  intro P M S _ _ a _ hpc1
  by_cases hc : 2 ≤ Fintype.card P
  · exact OnePseudoConsensus.nonUniform_inp hpc1 hc
  · exact absurd hpc1 (noPC1 a (by omega))

-- `Cslib.FLP.OnePseudoConsensus.nonUniform_init` idx 8: removable (dependent; 1-pseudo-consensus forces card P ≥ 2)
theorem nuin8 : indep% Cslib.FLP.OnePseudoConsensus.nonUniform_init 8 := by
  intro P M S _ _ a _ hpc1
  by_contra hc
  exact noPC1 a (by omega) hpc1

-- `Cslib.FLP.OnePseudoConsensus.not_terminating` idx 8: removable (1-pseudo-consensus forces card P ≥ 2)
theorem nt8 : drop% Cslib.FLP.OnePseudoConsensus.not_terminating 8 := by
  intro P M S _ _ a _ hpc1
  by_cases hc : 2 ≤ Fintype.card P
  · exact OnePseudoConsensus.not_terminating hpc1 hc
  · exact absurd hpc1 (noPC1 a (by omega))

-- `Cslib.FLP.OnePseudoConsensus.nonUniform_init` idx 7: necessary (dependent; flpAB is not 1-pseudo-consensus)
theorem nuin7 : ¬ indep0% Cslib.FLP.OnePseudoConsensus.nonUniform_init 7 := fun h => by
  obtain ⟨-, ht⟩ := @h Bool Unit Unit _ _ flpAB _ (by simp)
  obtain ⟨s', b, hc, hd⟩ := ht (fun _ => true) _ Algorithm.reachable_start Set.univ (by simp)
  exact noDecStart (fun _ _ => rfl) (CanReachVia.canReach hc) hd

-- `Cslib.FLP.OnePseudoConsensus.fair_nonUniform_step` idx 8: necessary (dependent; no 1-pseudo-consensus on Unit)
theorem fnus8 : ¬ indep0% Cslib.FLP.OnePseudoConsensus.fair_nonUniform_step 8 := fun h =>
  noPC1 flpA (by simp) (@h Unit Unit Unit _ _ flpA _ (fun _ => true))

-- `Cslib.FLP.OnePseudoConsensus.not_terminating` idx 7: necessary (ZeroFaultAlg on 2 processes terminates)
theorem nt7 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.not_terminating 7 := fun h => by
  obtain ⟨inp, ss, xs, hr, hn⟩ := @h (Fin 2) Bool Unit _ _ (Cslib.FLP.ZeroFaultAlg.alg (n := 2) (by decide)) _ (by simp)
  exact hn 0 ((Cslib.FLP.ZeroFaultAlg.consensus_zero (n := 2) (by decide)).2 inp ss xs hr 0)

-- `Cslib.FLP.Consensus.one_not_exists` idx 6: necessary (no processes: every algorithm is a consensus)
theorem one6 : ¬ drop0% Cslib.FLP.Consensus.one_not_exists 6 := fun h =>
  @h Empty Unit Unit _ _ _ ⟨flpE, fun _ _ _ => ⟨fun _ _ ⟨⟨p, _⟩, _⟩ => p.elim, fun _ ⟨p, _⟩ => p.elim⟩,
    fun _ _ _ _ p => p.elim⟩
where flpE : Algorithm Empty Unit Unit := ⟨fun _ => (), fun _ _ => (), fun _ _ => 0, fun _ _ => none⟩

-- `Cslib.FLP.Consensus.ge_one_not_exists` idx 7: necessary (no processes)
theorem geone7 : ¬ drop0% Cslib.FLP.Consensus.ge_one_not_exists 7 := fun h =>
  @h Empty Unit Unit _ _ _ 1 le_rfl ⟨one6.flpE, fun _ _ _ => ⟨fun _ _ ⟨⟨p, _⟩, _⟩ => p.elim, fun _ ⟨p, _⟩ => p.elim⟩,
    fun _ _ _ _ p => p.elim⟩


-- `Cslib.FLP.OnePseudoConsensus.canDecideWithout_uniform` idx 8: necessary (flpP: receiving the poison message
-- at process false destroys the only way to decide without process true)
theorem cdwu8 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.canDecideWithout_uniform 8 := fun h => by
  have hr : flpP.Reachable (fun _ => true) sP :=
    ⟨[some ⟨true, .inl true⟩], .single _ ⟨by simp [Algorithm.start], rfl⟩⟩
  have hm : (⟨false, .inr ()⟩ : Message Bool Unit) ∈ sP.msgs := by simp [sP, Algorithm.recvMsg, flpP]
  have hd : flpP.CanDecideWithout sP true true :=
    ⟨flpP.recvMsg ⟨false, .inl true⟩ sP,
      .single ⟨some ⟨false, .inl true⟩, by simp [DestIn], by simp [sP, Algorithm.recvMsg, Algorithm.start], rfl⟩,
      ⟨false, by simp [sP, Algorithm.recvMsg, Algorithm.start, flpP, State.ProcDecided]⟩⟩
  have hdn : ¬ flpP.CanDecideWithout sP true (!true) := by
    rintro ⟨u, hu, q, hq⟩
    obtain ⟨xl, hx⟩ := CanReachVia.canReach hu
    refine Pinv hx (fun q => ?_) q hq
    simp [sP, Algorithm.recvMsg, Algorithm.start, flpP]
  obtain ⟨u, hu, q, hq⟩ := @h Bool Unit Bool _ _ flpP (fun _ => true) _ sP _ _ true hr ⟨hm, rfl⟩ true hd hdn
  have hJ := Pinv2 hu (by simp [PJ, sP, Algorithm.recvMsg, Algorithm.start, flpP])
  obtain ⟨-, h2, h3⟩ := hJ
  cases q
  · have : (u.proc false).out = some true := hq
    rw [h2] at this; cases this
  · have : (u.proc true).out = some true := hq
    rw [h3] at this; cases this

-- `Cslib.FLP.OnePseudoConsensus.nonUniform_step_exists` idx 8: necessary (flpN: receiving m decides process false)
theorem nuse8 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.nonUniform_step_exists 8 := fun h => by
  obtain ⟨xl, t, hmt, hmx, -, hnt⟩ := @h Bool Unit Unit _ _ flpN _ id sN _ ⟨sN_reach, sN_nu⟩ (sN_mem false)
  obtain ⟨c, hc⟩ := nA hmt hmx
  exact flpN_uni (flpN_mtr_true hmt sN_true) hc hnt

-- `Cslib.FLP.OnePseudoConsensus.nonUniform_step_aux` idx 8: necessary (same flpN argument)
theorem nusa8 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.nonUniform_step_aux 8 := fun h => by
  obtain ⟨⟨xl, t⟩, hx⟩ := @h Bool Unit Unit _ _ flpN _ id sN ⟨false, .inl false⟩
  obtain ⟨hmt, hmx, -, hnt⟩ := hx ⟨sN_mem false, sN_reach, sN_nu⟩
  obtain ⟨c, hc⟩ := nA hmt hmx
  exact flpN_uni (flpN_mtr_true hmt sN_true) hc hnt

-- `Cslib.FLP.OnePseudoConsensus.fair_nonUniform` idx 8: necessary (flpN: fairness forces process false to decide,
-- after which no state is non-uniform)
theorem fnu8 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.fair_nonUniform 8 := fun h => by
  obtain ⟨ss, xs, he, h0, hf, hfreq⟩ := @h Bool Unit Unit _ _ flpN _ id sN ⟨sN_reach, sN_nu⟩
  obtain ⟨j, -, hj⟩ := hf false ⟨false, .inl false⟩ rfl 0 (by rw [h0]; exact sN_mem false)
  obtain ⟨n, hn, -, hnu⟩ := Filter.frequently_atTop.mp hfreq (j + 1)
  have hm := he.extract_mTr (Nat.zero_le j)
  have hm2 := he.extract_mTr hn
  have hstep := he j
  rw [hj] at hstep
  obtain ⟨-, hsj⟩ := hstep
  obtain ⟨c, hc⟩ := nRecv (ss j) false
  rw [← hsj] at hc
  have hc' := Algorithm.procDecided_stable (a := flpN) (p := false) (b := c) hc ⟨_, hm2⟩
  have htr : ((ss n).proc true).out = none :=
    flpN_mtr_true (he.extract_mTr (Nat.zero_le n)) (by rw [h0]; exact sN_true)
  exact flpN_uni htr hc' hnu

-- `Cslib.FLP.OnePseudoConsensus.canDecideWithout_uniform` idx 16: removable (hd follows from hpc1, hr and hdn:
-- canDecideWithout_exists gives some b' with CanDecideWithout s p b', and hdn rules out b' = !b)
theorem cdwu16 : drop% Cslib.FLP.OnePseudoConsensus.canDecideWithout_uniform 16 := by
  intro P M S _ _ a inp _ hpc1 s s' m b hr ht p hdn
  obtain ⟨b', hb'⟩ := OnePseudoConsensus.canDecideWithout_exists hpc1 hr p
  have : b' = b := by
    cases b <;> cases b' <;> first | rfl | exact absurd hb' hdn
  subst this
  exact OnePseudoConsensus.canDecideWithout_uniform hpc1 hr ht hb' hdn

end FLPV
end FLPS
