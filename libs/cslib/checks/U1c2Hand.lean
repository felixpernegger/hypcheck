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

namespace U1c2
open Cslib.Logic.Kleene
-- helpers: non-monotone extension of negation / meet / join (unknown ↦ true)
def fN : Value → Value := fun a => if a = .unknown then .true else aᶜ
def fI : Value → Value → Value := fun a b => if a = .unknown ∨ b = .unknown then .true else a ⊓ b
def fS : Value → Value → Value := fun a b => if a = .unknown ∨ b = .unknown then .true else a ⊔ b
end U1c2

-- `Cslib.Logic.Kleene.Value.InfoLE.trans` idx 3: necessary (a = true, b = unknown, c = false)
theorem k_trans3 : ¬ drop0% Cslib.Logic.Kleene.Value.InfoLE.trans 3 := fun h =>
  absurd (@h .true .unknown .false (by decide)) (by decide)

-- `Cslib.Logic.Kleene.Value.InfoLE.trans` idx 4: necessary (a = b = true, c = false)
theorem k_trans4 : ¬ drop0% Cslib.Logic.Kleene.Value.InfoLE.trans 4 := fun h =>
  absurd (@h .true .true .false (by decide)) (by decide)

-- `Cslib.Logic.Kleene.Value.InfoLE.antisymm` idx 2: necessary (a = true, b = unknown)
theorem k_anti2 : ¬ drop0% Cslib.Logic.Kleene.Value.InfoLE.antisymm 2 := fun h =>
  absurd (@h .true .unknown (by decide)) (by decide)

-- `Cslib.Logic.Kleene.Value.InfoLE.antisymm` idx 3: necessary (a = unknown, b = true)
theorem k_anti3 : ¬ drop0% Cslib.Logic.Kleene.Value.InfoLE.antisymm 3 := fun h =>
  absurd (@h .unknown .true (by decide)) (by decide)

-- `Cslib.Logic.Kleene.Value.InfoLE.compl` idx 2: necessary (a = true, a' = false)
theorem k_compl2 : ¬ drop0% Cslib.Logic.Kleene.Value.InfoLE.compl 2 := fun h =>
  absurd (@h .true .false) (by decide)

-- `Cslib.Logic.Kleene.Value.InfoLE.inf` idx 4: necessary (a = true, a' = false, b = b' = true)
theorem k_inf4 : ¬ drop0% Cslib.Logic.Kleene.Value.InfoLE.inf 4 := fun h =>
  absurd (@h .true .false .true .true (by decide)) (by decide)

-- `Cslib.Logic.Kleene.Value.InfoLE.inf` idx 5: necessary (a = a' = true, b = true, b' = false)
theorem k_inf5 : ¬ drop0% Cslib.Logic.Kleene.Value.InfoLE.inf 5 := fun h =>
  absurd (@h .true .true .true .false (by decide)) (by decide)

-- `Cslib.Logic.Kleene.Value.InfoLE.sup` idx 4: necessary (a = true, a' = false, b = b' = false)
theorem k_sup4 : ¬ drop0% Cslib.Logic.Kleene.Value.InfoLE.sup 4 := fun h =>
  absurd (@h .true .false .false .false (by decide)) (by decide)

-- `Cslib.Logic.Kleene.Value.InfoLE.sup` idx 5: necessary (a = a' = false, b = true, b' = false)
theorem k_sup5 : ¬ drop0% Cslib.Logic.Kleene.Value.InfoLE.sup 5 := fun h =>
  absurd (@h .false .false .true .false (by decide)) (by decide)

-- `Cslib.Logic.Kleene.Value.infoLE_compl_of_extends` idx 1: necessary (f unknown = true)
theorem k_cc1 : ¬ drop0% Cslib.Logic.Kleene.Value.infoLE_compl_of_extends 1 := fun h =>
  absurd (@h U1c2.fN (by decide) .unknown) (by decide)

-- `Cslib.Logic.Kleene.Value.infoLE_compl_of_extends` idx 2: necessary (f = id, a = true)
theorem k_cc2 : ¬ drop0% Cslib.Logic.Kleene.Value.infoLE_compl_of_extends 2 := fun h =>
  absurd (@h id (by decide) .true) (by decide)

-- `Cslib.Logic.Kleene.Value.eq_compl_of_extends` idx 1: necessary (f unknown = true)
theorem k_ec1 : ¬ drop0% Cslib.Logic.Kleene.Value.eq_compl_of_extends 1 := fun h =>
  absurd (@h U1c2.fN (by decide) .unknown) (by decide)

-- `Cslib.Logic.Kleene.Value.eq_compl_of_extends` idx 2: necessary (f = id, a = true)
theorem k_ec2 : ¬ drop0% Cslib.Logic.Kleene.Value.eq_compl_of_extends 2 := fun h =>
  absurd (@h id (by decide) .true) (by decide)

-- `Cslib.Logic.Kleene.Value.infoLE_inf_of_extends` idx 1: necessary (f = true if an argument is unknown)
theorem k_ci1 : ¬ drop0% Cslib.Logic.Kleene.Value.infoLE_inf_of_extends 1 := fun h =>
  absurd (@h U1c2.fI (by decide) .unknown .unknown) (by decide)

-- `Cslib.Logic.Kleene.Value.infoLE_inf_of_extends` idx 2: necessary (f = first projection, a = true, b = false)
theorem k_ci2 : ¬ drop0% Cslib.Logic.Kleene.Value.infoLE_inf_of_extends 2 := fun h =>
  absurd (@h (fun a _ => a) (by decide) .true .false) (by decide)

-- `Cslib.Logic.Kleene.Value.infoLE_sup_of_extends` idx 1: necessary (f = true if an argument is unknown)
theorem k_cs1 : ¬ drop0% Cslib.Logic.Kleene.Value.infoLE_sup_of_extends 1 := fun h =>
  absurd (@h U1c2.fS (by decide) .unknown .unknown) (by decide)

-- `Cslib.Logic.Kleene.Value.infoLE_sup_of_extends` idx 2: necessary (f = first projection, a = false, b = true)
theorem k_cs2 : ¬ drop0% Cslib.Logic.Kleene.Value.infoLE_sup_of_extends 2 := fun h =>
  absurd (@h (fun a _ => a) (by decide) .false .true) (by decide)

namespace U1c2
open Cslib.Circuits
-- signature with a nullary op `false` and a unary op `true`
def sg : Signature.{0} := ⟨Bool, fun b => cond b 1 0⟩
def l0 {n m : ℕ} : Line sg n m := ⟨false, nofun⟩
def l1 {n m : ℕ} (w : Wire n m) : Line sg n m := ⟨true, fun _ => w⟩
end U1c2

-- `Cslib.Circuits.Circuit.ext` idx 5: necessary (a circuit with 0 gates and one with 1 gate)
theorem c_ext5 : ¬ indep0% Cslib.Circuits.Circuit.ext 5 := fun h =>
  absurd (@h U1c2.sg 0 0 ⟨.empty, nofun⟩ ⟨.gate .empty U1c2.l0, nofun⟩) (by decide)

-- `Cslib.Circuits.Circuit.ext` idx 6: necessary (same outputs, programs with gates `false` / `true`)
theorem c_ext6 : ¬ drop0% Cslib.Circuits.Circuit.ext 6 := fun h => by
  have := @h U1c2.sg 1 0 ⟨.gate .empty U1c2.l0, nofun⟩ ⟨.gate .empty (U1c2.l1 (.input 0)), nofun⟩ rfl
    (by funext i; exact i.elim0)
  have h2 := Cslib.Circuits.Circuit.mk.inj this
  have h3 := eq_of_heq h2.2.1
  injection h3 with _ h4 h5
  have := congrArg Cslib.Circuits.Line.op h5
  simp [U1c2.l0, U1c2.l1] at this

-- `Cslib.Circuits.Circuit.ext` idx 7: necessary (empty programs, outputs input 0 vs input 1)
theorem c_ext7 : ¬ drop0% Cslib.Circuits.Circuit.ext 7 := fun h => by
  have := @h U1c2.sg 2 1 ⟨.empty, fun _ => .input 0⟩ ⟨.empty, fun _ => .input 1⟩ rfl rfl
  have h2 := Cslib.Circuits.Circuit.mk.inj this
  have h3 := congrFun (eq_of_heq h2.2.2) 0
  simp at h3

-- `Cslib.Circuits.Line.ext` idx 5: necessary (lines with different operations)
theorem c_line5 : ¬ indep0% Cslib.Circuits.Line.ext 5 := fun h =>
  absurd (@h U1c2.sg 1 0 U1c2.l0 (U1c2.l1 (.input 0))) (by simp [U1c2.l0, U1c2.l1])

-- `Cslib.Circuits.Line.ext` idx 6: necessary (same operation, wires input 0 vs input 1)
theorem c_line6 : ¬ drop0% Cslib.Circuits.Line.ext 6 := fun h => by
  have : Cslib.Circuits.Line.mk (σ := U1c2.sg) true (fun _ => Cslib.Circuits.Wire.input (0 : Fin 2)) = (⟨true, fun _ => Cslib.Circuits.Wire.input (1 : Fin 2)⟩ : Cslib.Circuits.Line U1c2.sg 2 0) := @h U1c2.sg 2 0 (U1c2.l1 (.input 0)) (U1c2.l1 (.input 1)) rfl
  have h2 := Cslib.Circuits.Line.mk.inj this
  have h3 := congrFun (eq_of_heq h2.2) (0 : Fin 1)
  simp at h3

-- `Cslib.Circuits.Program.trace_congr` idx 9: necessary (inputs differ, wire is the input)
theorem c_trace9 : ¬ drop0% Cslib.Circuits.Program.trace_congr 9 := fun h =>
  absurd (@h U1c2.sg 1 0 ℕ .empty (fun _ _ => 0) (fun _ => 0) (fun _ => 1) (.input 0)) (by simp [Cslib.Circuits.Program.trace])

namespace U1c2
open Turing Turing.MultiTapeTM
-- helpers (from W2c4): `nop1` computes [] in time 1, space 1; outputs have length at most the time bound
def encC (l : List Bool) : Unit ↪ List Bool := ⟨fun _ => l, fun _ _ _ => rfl⟩
abbrev nop1 : Turing.MultiTapeTM 1 Bool Unit := Turing.MultiTapeTM.nop 1 Bool
theorem nopPos {input : List Bool} (c : Turing.Cfg 1 Bool Unit input) (n : ℕ) :
    (nop1.runFrom c n).workTapePos 0 = c.workTapePos 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Turing.MultiTapeTM.runFrom, Function.iterate_succ_apply', ← Turing.MultiTapeTM.runFrom]
    rcases hq : (nop1.runFrom c n).state with _ | q
    · rw [Turing.MultiTapeTM.step_of_halt hq, ih]
    · rw [Turing.MultiTapeTM.step_workTapePos_of_state hq, ih]
      simp [Turing.MultiTapeTM.nop]
theorem nopSpace (input : List Bool) : nop1.RunsInSpace input 1 := fun q => by
  refine (Turing.MultiTapeNTM.RunPath.space_le_sum_card q.toRunPath (S := fun _ => {0}) ?_).trans
    (by simp)
  rintro c ⟨i, rfl⟩ j
  rw [Subsingleton.elim j 0]
  change (q.toRunPath i).workTapePos 0 ∈ ({0} : Finset ℤ)
  rw [Turing.MultiTapeTM.runPath_apply_eq_runFrom, nopPos, q.head_eq]
  simp
theorem nopComp : nop1.ComputesInTimeAndSpace [] [] 1 1 := by
  have h1 : nop1.runFrom (nop1.initCfg []) 1 = ⟨none, 1, fun _ _ => none, fun _ => 0, []⟩ := by
    rw [Turing.MultiTapeTM.runFrom, Function.iterate_one,
      Turing.MultiTapeTM.step_of_state (q := ()) rfl]
    ext <;> simp [Turing.MultiTapeTM.nop, Turing.Action.apply, SignType.cast]
  refine ⟨⟨1, by rw [h1], by rw [h1]⟩, Turing.MultiTapeTM.runsInTime_of_halted (by rw [h1]), nopSpace _⟩
theorem outLen {k : ℕ} {Sy St : Type} (tm : Turing.MultiTapeTM k Sy St) {input : List Sy}
    (c : Turing.Cfg k Sy St input) (u : ℕ) :
    (tm.runFrom c u).output.length ≤ c.output.length + u := by
  induction u with
  | zero => simp [Turing.MultiTapeTM.runFrom]
  | succ u ih =>
    rw [Turing.MultiTapeTM.runFrom, Function.iterate_succ_apply', ← Turing.MultiTapeTM.runFrom]
    rcases hq : (tm.runFrom c u).state with _ | q
    · rw [Turing.MultiTapeTM.step_of_halt hq]; omega
    · rw [Turing.MultiTapeTM.step_of_state hq]
      simp only [Turing.Action.apply_output, List.length_append]
      generalize (tm.tr q _ _).output = o
      cases o <;> simp <;> omega
theorem outBound {k : ℕ} {St : Type} {tm : Turing.MultiTapeTM k Bool St} {input output : List Bool}
    {t s : ℕ} (h : tm.ComputesInTimeAndSpace input output t s) : output.length ≤ t := by
  obtain ⟨⟨u, hu, ho⟩, ht, -⟩ := h
  have hT : (tm.runFrom (tm.initCfg input) t).Halted :=
    ht (Turing.MultiTapeNTM.ComputationPath.ofDeterministic tm input t) le_rfl
  rcases le_total u t with hut | htu
  · have := outLen tm (tm.initCfg input) u
    rw [ho] at this; simp at this; omega
  · rw [Turing.MultiTapeTM.runFrom_eq_of_halt tm _ htu hT] at ho
    have := outLen tm (tm.initCfg input) t
    rw [ho] at this; simp at this; omega
def r6 : List Bool := List.replicate 6 true
-- a length-0 run path ends where it starts
theorem len0 {M : Turing.MultiTapeNTM k Sy St} {input : List Sy} (q : M.RunPath input) (h : q.length = 0) :
    q.last = q.head := by
  have : Fin.last q.length = 0 := Fin.ext (by simp [h])
  show q (Fin.last _) = q 0
  rw [this]
def ntm1 : Turing.MultiTapeNTM 1 Bool Unit := ⟨(), fun _ _ _ _ => False⟩
def cH0 : Turing.Cfg 0 Bool Unit [] := ⟨none, 0, fun _ _ => none, fun _ => 0, []⟩
def eId (k : ℕ) : Fin k ↪ Fin k := ⟨id, fun _ _ h => h⟩
def cW : Turing.Cfg 1 Bool Unit [] := ⟨none, 0, fun _ _ => some true, fun _ => 1, []⟩
end U1c2

-- `Turing.MultiTapeNTM.RunsInSpace.numTapes_le` idx 6: necessary (1 work tape, space 0)
theorem t_ntl6 : ¬ drop0% Turing.MultiTapeNTM.RunsInSpace.numTapes_le 6 := fun h =>
  absurd (h (k := 1) (Symbol := Bool) (State := Unit) (ntm := U1c2.ntm1) (input := []) (s := 0)) (by decide)

-- `Turing.MultiTapeTM.ComputesInTimeAndSpace.concatenate` idx 14: necessary (out₁ of length 6 in time 0)
theorem t_cc14 : ¬ drop0% Turing.MultiTapeTM.ComputesInTimeAndSpace.concatenate 14 := fun h => by
  have := U1c2.outBound (h (tm₁ := U1c2.nop1) (tm₂ := U1c2.nop1) (input := []) (out₁ := U1c2.r6) (out₂ := [])
    (t₁ := 0) (t₂ := 1) (s₁ := 0) (s₂ := 1) U1c2.nopComp)
  simp [U1c2.r6] at this

-- `Turing.MultiTapeTM.ComputesInTimeAndSpace.concatenate` idx 15: necessary (out₂ of length 6 in time 0)
theorem t_cc15 : ¬ drop0% Turing.MultiTapeTM.ComputesInTimeAndSpace.concatenate 15 := fun h => by
  have := U1c2.outBound (h (tm₁ := U1c2.nop1) (tm₂ := U1c2.nop1) (input := []) (out₁ := []) (out₂ := U1c2.r6)
    (t₁ := 1) (t₂ := 0) (s₁ := 1) (s₂ := 0) U1c2.nopComp)
  simp [U1c2.r6] at this

-- `Turing.MultiTapeTM.ComputesFunInTimeAndSpace.concatenate` idx 22: necessary
theorem t_cf22 : ¬ drop0% Turing.MultiTapeTM.ComputesFunInTimeAndSpace.concatenate 22 := fun h => by
  have := U1c2.outBound (h (tm₁ := U1c2.nop1) (tm₂ := U1c2.nop1) (α := Unit) (β := Unit) (γ := Unit) (δ := Unit)
    (f₁ := fun _ => ()) (f₂ := fun _ => ()) (f := fun _ => ()) (encIn := U1c2.encC [])
    (enc₁ := U1c2.encC U1c2.r6) (enc₂ := U1c2.encC []) (encOut := U1c2.encC U1c2.r6)
    (t₁ := fun _ => 0) (t₂ := fun _ => 1) (s₁ := fun _ => 0) (s₂ := fun _ => 1)
    (fun _ => U1c2.nopComp) (fun _ => rfl) ())
  simp [U1c2.r6, U1c2.encC] at this

-- `Turing.MultiTapeTM.ComputesFunInTimeAndSpace.concatenate` idx 23: necessary
theorem t_cf23 : ¬ drop0% Turing.MultiTapeTM.ComputesFunInTimeAndSpace.concatenate 23 := fun h => by
  have := U1c2.outBound (h (tm₁ := U1c2.nop1) (tm₂ := U1c2.nop1) (α := Unit) (β := Unit) (γ := Unit) (δ := Unit)
    (f₁ := fun _ => ()) (f₂ := fun _ => ()) (f := fun _ => ()) (encIn := U1c2.encC [])
    (enc₁ := U1c2.encC []) (enc₂ := U1c2.encC U1c2.r6) (encOut := U1c2.encC U1c2.r6)
    (t₁ := fun _ => 1) (t₂ := fun _ => 0) (s₁ := fun _ => 1) (s₂ := fun _ => 0)
    (fun _ => U1c2.nopComp) (fun _ => rfl) ())
  simp [U1c2.r6, U1c2.encC] at this

-- `Turing.MultiTapeTM.ComputesFunInTimeAndSpace.concatenate` idx 24: necessary (encOut ≠ enc₁ ++ enc₂)
theorem t_cf24 : ¬ drop0% Turing.MultiTapeTM.ComputesFunInTimeAndSpace.concatenate 24 := fun h => by
  have := U1c2.outBound (h (tm₁ := U1c2.nop1) (tm₂ := U1c2.nop1) (α := Unit) (β := Unit) (γ := Unit) (δ := Unit)
    (f₁ := fun _ => ()) (f₂ := fun _ => ()) (f := fun _ => ()) (encIn := U1c2.encC [])
    (enc₁ := U1c2.encC []) (enc₂ := U1c2.encC []) (encOut := U1c2.encC U1c2.r6)
    (t₁ := fun _ => 1) (t₂ := fun _ => 1) (s₁ := fun _ => 1) (s₂ := fun _ => 1)
    (fun _ => U1c2.nopComp) (fun _ => U1c2.nopComp) ())
  simp [U1c2.r6, U1c2.encC] at this

-- `Turing.MultiTapeTM.ComputableInTimeAndSpace.concatenate` idx 15: necessary
theorem t_cb15 : ¬ drop0% Turing.MultiTapeTM.ComputableInTimeAndSpace.concatenate 15 := fun h => by
  obtain ⟨k, S, _, tm, htm⟩ := h (α := Unit) (β := Unit) (γ := Unit) (δ := Unit)
    (f₁ := fun _ => ()) (f₂ := fun _ => ()) (f := fun _ => ()) (encIn := U1c2.encC [])
    (enc₁ := U1c2.encC U1c2.r6) (enc₂ := U1c2.encC []) (encOut := U1c2.encC U1c2.r6)
    (t₁ := fun _ => 0) (t₂ := fun _ => 1) (s₁ := fun _ => 0) (s₂ := fun _ => 1)
    ⟨1, Unit, inferInstance, U1c2.nop1, fun _ => U1c2.nopComp⟩ (fun _ => rfl)
  have := U1c2.outBound (htm ())
  simp [U1c2.r6, U1c2.encC] at this

-- `Turing.MultiTapeTM.ComputableInTimeAndSpace.concatenate` idx 16: necessary
theorem t_cb16 : ¬ drop0% Turing.MultiTapeTM.ComputableInTimeAndSpace.concatenate 16 := fun h => by
  obtain ⟨k, S, _, tm, htm⟩ := h (α := Unit) (β := Unit) (γ := Unit) (δ := Unit)
    (f₁ := fun _ => ()) (f₂ := fun _ => ()) (f := fun _ => ()) (encIn := U1c2.encC [])
    (enc₁ := U1c2.encC []) (enc₂ := U1c2.encC U1c2.r6) (encOut := U1c2.encC U1c2.r6)
    (t₁ := fun _ => 1) (t₂ := fun _ => 0) (s₁ := fun _ => 1) (s₂ := fun _ => 0)
    ⟨1, Unit, inferInstance, U1c2.nop1, fun _ => U1c2.nopComp⟩ (fun _ => rfl)
  have := U1c2.outBound (htm ())
  simp [U1c2.r6, U1c2.encC] at this

-- `Turing.MultiTapeTM.ComputableInTimeAndSpace.concatenate` idx 17: necessary
theorem t_cb17 : ¬ drop0% Turing.MultiTapeTM.ComputableInTimeAndSpace.concatenate 17 := fun h => by
  obtain ⟨k, S, _, tm, htm⟩ := h (α := Unit) (β := Unit) (γ := Unit) (δ := Unit)
    (f₁ := fun _ => ()) (f₂ := fun _ => ()) (f := fun _ => ()) (encIn := U1c2.encC [])
    (enc₁ := U1c2.encC []) (enc₂ := U1c2.encC []) (encOut := U1c2.encC U1c2.r6)
    (t₁ := fun _ => 1) (t₂ := fun _ => 1) (s₁ := fun _ => 1) (s₂ := fun _ => 1)
    ⟨1, Unit, inferInstance, U1c2.nop1, fun _ => U1c2.nopComp⟩
    ⟨1, Unit, inferInstance, U1c2.nop1, fun _ => U1c2.nopComp⟩
  have := U1c2.outBound (htm ())
  simp [U1c2.r6, U1c2.encC] at this

-- `Turing.MultiTapeTM.embed_workTapes_of_notMem_range` idx 10: necessary (e = id, cfg tape ≠ extra tape)
theorem t_emb10 : ¬ drop0% Turing.MultiTapeTM.embed_workTapes_of_notMem_range 10 := fun h => by
  have h1 := h (U1c2.eId 1) U1c2.cW (fun _ _ => none) (fun _ => 0) (l := 0)
  have h2 := Turing.MultiTapeTM.embed_workTapes_embed (U1c2.eId 1) U1c2.cW (fun _ _ => none) (fun _ => 0) 0
  have h3 := congrFun (h2.symm.trans h1) 0
  simp [U1c2.cW] at h3

-- `Turing.MultiTapeTM.embed_workTapePos_of_notMem_range` idx 10: necessary (e = id, head 1 ≠ extra head 0)
theorem t_emb10' : ¬ drop0% Turing.MultiTapeTM.embed_workTapePos_of_notMem_range 10 := fun h => by
  have h1 := h (U1c2.eId 1) U1c2.cW (fun _ _ => none) (fun _ => 0) (l := 0)
  have h2 := Turing.MultiTapeTM.embed_workTapePos_embed (U1c2.eId 1) U1c2.cW (fun _ _ => none) (fun _ => 0) 0
  have h3 := h2.symm.trans h1
  simp [U1c2.cW] at h3

-- `Turing.MultiTapeTM.embed_eq_of_forall_embed` idx 9: necessary (tapes ≠ cfg tapes)
theorem t_emb9 : ¬ drop0% Turing.MultiTapeTM.embed_eq_of_forall_embed 9 := fun h => by
  have h1 := congrArg Turing.Cfg.workTapes
    (h (U1c2.eId 1) U1c2.cW (tapes := fun _ _ => none) (heads := fun _ => 1) (fun _ => rfl))
  have h2 := Turing.MultiTapeTM.embed_workTapes_embed (U1c2.eId 1) U1c2.cW (fun _ _ => none) (fun _ => 1) 0
  have h3 := congrFun (h2.symm.trans (congrFun h1 0)) 0
  simp [U1c2.cW] at h3

-- `Turing.MultiTapeTM.embed_eq_of_forall_embed` idx 10: necessary (heads ≠ cfg heads)
theorem t_emb10'' : ¬ drop0% Turing.MultiTapeTM.embed_eq_of_forall_embed 10 := fun h => by
  have h1 := congrArg Turing.Cfg.workTapePos
    (h (U1c2.eId 1) U1c2.cW (tapes := fun _ _ => some true) (heads := fun _ => 0) (fun _ => rfl))
  have h2 := Turing.MultiTapeTM.embed_workTapePos_embed (U1c2.eId 1) U1c2.cW (fun _ _ => some true) (fun _ => 0) 0
  have h3 := h2.symm.trans (congrFun h1 0)
  simp [U1c2.cW] at h3

-- `Turing.MultiTapeTM.exists_runPath_extendTapes` idx 8: necessary (singleton path at a halted configuration, k = 0)
theorem t_ex8 : ¬ drop0% Turing.MultiTapeTM.exists_runPath_extendTapes 8 := fun h => by
  obtain ⟨q, hq1, hq2, hq3, -⟩ := h (k := 0) (k' := 0) (Symbol := Bool) (State := Unit)
    (input := []) (tm := Turing.MultiTapeTM.nop 0 Bool) (U1c2.eId 0)
    (p := RelSeries.singleton _ U1c2.cH0) [] (tapes := fun _ _ => none) (heads := fun _ => 0)
    (fun j => j.elim0) (fun j => j.elim0)
  have h0 := U1c2.len0 q (by simpa using hq3)
  rw [hq1, hq2] at h0
  have := congrArg Turing.Cfg.state h0
  simp [Turing.MultiTapeTM.embed, U1c2.cH0, Turing.Cfg.prependOutput] at this

-- `Turing.MultiTapeTM.exists_runPath_extendTapes` idx 12: necessary (initial path, tapes of the range not blank)
theorem t_ex12 : ¬ drop0% Turing.MultiTapeTM.exists_runPath_extendTapes 12 := fun h => by
  obtain ⟨q, hq1, hq2, hq3, -⟩ := h (k := 1) (k' := 1) (Symbol := Bool) (State := Unit)
    (input := []) (tm := U1c2.nop1) (U1c2.eId 1)
    (p := RelSeries.singleton _ (U1c2.nop1.initCfg [])) rfl [] (tapes := fun _ _ => some true)
    (heads := fun _ => 0) (fun _ => rfl)
  have h0 := U1c2.len0 q (by simpa using hq3)
  rw [hq1, hq2] at h0
  have := congrArg (fun c => c.workTapes 0 0) h0
  simp [Turing.MultiTapeTM.embed, Turing.Cfg.prependOutput, Turing.Cfg.init, U1c2.eId, Turing.MultiTapeTM.partialInv] at this

-- `Turing.MultiTapeTM.exists_runPath_extendTapes` idx 13: necessary (initial path, heads of the range not at 0)
theorem t_ex13 : ¬ drop0% Turing.MultiTapeTM.exists_runPath_extendTapes 13 := fun h => by
  obtain ⟨q, hq1, hq2, hq3, -⟩ := h (k := 1) (k' := 1) (Symbol := Bool) (State := Unit)
    (input := []) (tm := U1c2.nop1) (U1c2.eId 1)
    (p := RelSeries.singleton _ (U1c2.nop1.initCfg [])) rfl [] (tapes := fun _ _ => none)
    (heads := fun _ => 1) (fun _ => rfl)
  have h0 := U1c2.len0 q (by simpa using hq3)
  rw [hq1, hq2] at h0
  have := congrArg (fun c => c.workTapePos 0) h0
  simp [Turing.MultiTapeTM.embed, Turing.Cfg.prependOutput, Turing.Cfg.init, U1c2.eId, Turing.MultiTapeTM.partialInv] at this

-- `_private.Cslib.Computability.Machines.Turing.MultiTape.Combinators.Concatenate.0.Turing.MultiTapeTM.Concatenate.first_phase` idx 7: necessary (singleton path at a halted configuration, k = 0)
theorem t_fp7 : ¬ drop0% _private.Cslib.Computability.Machines.Turing.MultiTape.Combinators.Concatenate.«0».Turing.MultiTapeTM.Concatenate.first_phase 7 := fun h => by
  obtain ⟨q, hq1, hq2, hq3, -⟩ := h (k₁ := 0) (k₂ := 0) (Symbol := Bool) (State₁ := Unit)
    (input := []) (tm := Turing.MultiTapeTM.nop 0 Bool) (p := RelSeries.singleton _ U1c2.cH0)
  have h0 := U1c2.len0 q (by simpa using hq3)
  rw [hq1, hq2] at h0
  have := congrArg Turing.Cfg.state h0
  simp [Turing.MultiTapeTM.embed, U1c2.cH0] at this

-- `_private.Cslib.Computability.Machines.Turing.MultiTape.Combinators.Concatenate.0.Turing.MultiTapeTM.Concatenate.third_phase` idx 8: necessary (singleton path at a halted configuration, k = 0)
theorem t_tp8 : ¬ drop0% _private.Cslib.Computability.Machines.Turing.MultiTape.Combinators.Concatenate.«0».Turing.MultiTapeTM.Concatenate.third_phase 8 := fun h => by
  obtain ⟨q, hq1, hq2, hq3, -⟩ := h (k₁ := 0) (k₂ := 0) (Symbol := Bool) (State₂ := Unit) (State₁ := Unit)
    (input := []) (tm := Turing.MultiTapeTM.nop 0 Bool) (p := RelSeries.singleton _ U1c2.cH0) U1c2.cH0
  have h0 := U1c2.len0 q (by simpa using hq3)
  rw [hq1, hq2] at h0
  have := congrArg Turing.Cfg.state h0
  simp [Turing.MultiTapeTM.embed, U1c2.cH0, Turing.Cfg.prependOutput] at this
