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

namespace W1c0

section circuits
open Cslib.Circuits Cslib.Circuits.Boolean

-- the input index of a wire in a gate-free program
def wireIdx : Wire 2 0 → Fin 2
  | .input i => i
  | .gate j => j.elim0

-- no program with at most one gate on two inputs computes F, if F is neither an input nor one gate on inputs
theorem oneGate (F : (Fin 2 → Bool) → Bool)
    (hi : ∀ i : Fin 2, (fun x : Fin 2 → Bool => x i) ≠ F)
    (hg : ∀ (op : Op) (w : Fin (signature.Arity op) → Fin 2),
      (fun x : Fin 2 → Bool => interpretation op (fun k => x (w k))) ≠ F)
    {g : ℕ} (p : Program signature 2 g) (hp : g ≤ 1) : F ∉ available interpretation p := by
  rintro ⟨w, hw⟩
  cases p with
  | empty =>
    cases w with
    | input i => exact hi i hw
    | gate k => exact k.elim0
  | gate q line =>
    cases q with
    | gate _ _ => omega
    | empty =>
      cases w with
      | input i => exact hi i hw
      | gate k =>
        obtain rfl : k = 0 := Fin.ext (by have := k.isLt; omega)
        apply hg line.op (wireIdx ∘ line.wires)
        rw [← hw]
        funext x
        simp only [Program.wireFunction, Program.trace, Wire.elim, Program.eval, Line.eval]
        congr 1
        funext k
        simp only [Function.comp]
        rcases line.wires k with i | j
        · rfl
        · exact j.elim0

-- the index of a wire in a one-gate program on two inputs (gate ↦ 2)
def wireIdx1 : Wire 2 1 → Fin 3
  | .input i => i.castSucc
  | .gate _ => 2

-- the value table of the three wires of a one-gate program
def ext3 (x : Fin 2 → Bool) (v : Bool) : Fin 3 → Bool := ![x 0, x 1, v]

-- no program with at most two gates on two inputs computes F, if F avoids all such shapes
theorem twoGate (F : (Fin 2 → Bool) → Bool)
    (hi : ∀ i : Fin 2, (fun x : Fin 2 → Bool => x i) ≠ F)
    (hg : ∀ (op : Op) (w : Fin (signature.Arity op) → Fin 2),
      (fun x : Fin 2 → Bool => interpretation op (fun k => x (w k))) ≠ F)
    (hg2 : ∀ (op : Op) (w : Fin (signature.Arity op) → Fin 2) (op' : Op)
      (w' : Fin (signature.Arity op') → Fin 3),
      (fun x : Fin 2 → Bool => interpretation op'
        (fun k => ext3 x (interpretation op (fun j => x (w j))) (w' k))) ≠ F)
    {g : ℕ} (p : Program signature 2 g) (hp : g ≤ 2) : F ∉ available interpretation p := by
  cases p with
  | empty => exact oneGate F hi hg .empty (by omega)
  | gate q line =>
    cases q with
    | empty => exact oneGate F hi hg (.gate .empty line) (by omega)
    | gate q' line1 =>
      cases q' with
      | gate _ _ => omega
      | empty =>
        rintro ⟨w, hw⟩
        have e1 : ∀ x (k : Fin (signature.Arity line1.op)),
            Wire.elim x (Program.eval (Program.empty) interpretation x) (line1.wires k) = x (wireIdx (line1.wires k)) := by
          intro x k
          rcases line1.wires k with i | j
          · rfl
          · exact j.elim0
        have e2 : ∀ x (k : Fin (signature.Arity line.op)),
            Wire.elim x ((Program.empty.gate line1).eval interpretation x) (line.wires k) =
              ext3 x (interpretation line1.op (fun j => x (wireIdx (line1.wires j)))) (wireIdx1 (line.wires k)) := by
          intro x k
          rcases line.wires k with i | j
          · fin_cases i <;> rfl
          · obtain rfl : j = 0 := Fin.ext (by have := j.isLt; omega)
            show (Program.empty.gate line1).eval interpretation x (Fin.last 0) = _
            rw [Program.eval_gate_last]
            unfold Line.eval
            show interpretation line1.op _ = interpretation line1.op _
            congr 1; funext j; exact e1 x j
        cases w with
        | input i => exact hi i hw
        | gate k =>
          rcases k with ⟨_ | _ | k, hk⟩
          · apply hg line1.op (wireIdx ∘ line1.wires)
            rw [← hw]
            funext x
            show _ = ((Program.empty.gate line1).gate line).eval interpretation x
              (Fin.castSucc (Fin.last 0))
            rw [Program.eval_gate_castSucc, Program.eval_gate_last]
            unfold Line.eval
            congr 1; funext j; exact (e1 x j).symm
          · apply hg2 line1.op (wireIdx ∘ line1.wires) line.op (wireIdx1 ∘ line.wires)
            rw [← hw]
            funext x
            show _ = ((Program.empty.gate line1).gate line).eval interpretation x (Fin.last 1)
            rw [Program.eval_gate_last]
            unfold Line.eval
            congr 1; funext k; exact (e2 x k).symm
          · omega

def xor2 : (Fin 2 → Bool) → Bool := fun x => x 0 != x 1
theorem xor2_no {g : ℕ} (p : Program signature 2 g) (hp : g ≤ 2) : xor2 ∉ available interpretation p :=
  twoGate _ (by decide) (by decide) (by decide) p hp

def nand2 : (Fin 2 → Bool) → Bool := fun x => !(x 0 && x 1)
theorem nand2_no {g : ℕ} (p : Program signature 2 g) (hp : g ≤ 1) : nand2 ∉ available interpretation p :=
  oneGate _ (by decide) (by decide) p hp

-- no zero-gate circuit computes the constant true function
theorem noZeroTrue (n : ℕ) (c : Circuit signature n 1)
    (hc : c.ComputesOn interpretation Set.univ (single fun _ => true)) : 1 ≤ c.size := by
  rcases c with ⟨_ | ⟨p, l⟩, out⟩
  · have := congrFun (hc (Set.mem_univ (fun _ => false))) 0
    cases h : out 0 with
    | input i => simp [Circuit.eval, h, single] at this
    | gate g => exact g.elim0
  · simp

-- 3k ≤ 2^k from k = 4 on
theorem three_mul_le_two_pow (k : ℕ) (hk : 4 ≤ k) : 3 * k ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ]; omega

-- 29 n ≤ 2^n from n = 10 on
theorem t29 (n : ℕ) (hn : 10 ≤ n) : 29 * n ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ]; omega

-- 16m² + 6m + 1 ≤ 2^m from m = 12 on
theorem poly_le_two_pow (m : ℕ) (hm : 12 ≤ m) : 16 * m ^ 2 + 6 * m + 1 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ 2 k]; nlinarith

-- Lupanov's bound with block size 0 and k = d = m is below 2^(2m)/(2m) from m = 12 on
theorem bound00_le (m : ℕ) (hm : 12 ≤ m) :
    Cslib.Circuits.Boolean.Lupanov.bound m m 0 * (m + m) ≤ 2 ^ (m + m) := by
  have hP := poly_le_two_pow m hm
  simp only [Cslib.Circuits.Boolean.Lupanov.bound, Nat.div_zero, pow_zero, pow_add]
  set A := 2 ^ m
  have h10 : 10 * m ≤ A := by nlinarith
  nlinarith [Nat.mul_le_mul_left A hP]

-- with block size 0, some function on m + m inputs needs more than bound m m 0 gates
theorem hard00 : ∃ m, 12 ≤ m ∧ ∃ f : Cslib.BooleanFunction (m + m), ∀ c : Circuit signature (m + m) 1,
    c.Computes interpretation (single f) → Cslib.Circuits.Boolean.Lupanov.bound m m 0 < c.size := by
  obtain ⟨N, hN⟩ := Cslib.Circuits.Boolean.Shannon.exists_hard_function
  obtain ⟨m, hm⟩ : ∃ m, m = max N 12 := ⟨_, rfl⟩
  refine ⟨m, by omega, ?_⟩
  obtain ⟨f, hf⟩ := hN (m + m) (by omega)
  refine ⟨f, fun c hc => ?_⟩
  have hlt := hf c hc
  have hb := bound00_le m (by omega)
  have hpos : (0 : ℝ) < ((m + m : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < m + m)
  rw [div_lt_iff₀ (by exact_mod_cast hpos)] at hlt
  have hb' : ((Cslib.Circuits.Boolean.Lupanov.bound m m 0 * (m + m) : ℕ) : ℝ) ≤ ((2 ^ (m + m) : ℕ) : ℝ) := by
    exact_mod_cast hb
  push_cast at hb' hlt hpos
  have : (Cslib.Circuits.Boolean.Lupanov.bound m m 0 : ℝ) < c.size := by nlinarith
  exact_mod_cast this
end circuits

section query
-- an oracle for arithmetic queries on ℕ
def arOr : {ι : Type} → Cslib.Query.ArithQuery ℕ ι → ι
  | _, .add a b => a + b
  | _, .sub a b => a - b
  | _, .mul a b => a * b

-- an oracle for comparison queries answering by le
def leOr {α : Type} (le : α → α → Bool) : {ι : Type} → Cslib.Query.LEQuery α ι → ι
  | _, .le a b => le a b

-- query functors with no queries and with one 3-answer query
inductive Q0 : Type → Type
inductive Q3 : Type → Type
  | q : Q3 (Fin 3)
def q3Or (i : Fin 3) : {ρ : Type} → Q3 ρ → ρ
  | _, .q => i

-- merge sort after reversing the input is a correct sort
theorem revSort {α : Type} : Cslib.Query.IsSort (fun xs : List α => Cslib.Query.mergeSort xs.reverse) where
  perm xs o := (Cslib.Query.mergeSort_isSort.perm xs.reverse o).trans (List.reverse_perm xs)
  sorted xs o r _ _ _ h := Cslib.Query.mergeSort_isSort.sorted xs.reverse o r h

def rps : Fin 3 → Fin 3 → Prop := fun a b => a = b ∨ b = a + 1
instance : DecidableRel rps := fun a b => by unfold rps; infer_instance
instance : Std.Total rps := ⟨by decide⟩
instance : Std.Antisymm rps := ⟨by decide⟩

-- bind-counting monad (not lawful)
@[instance_reducible] def cntM : Monad (fun α => ℕ × α) where
  pure a := (0, a)
  bind x f := ((f x.2).1 + x.1 + 1, (f x.2).2)
-- a list pairwise related by the empty relation has at most one element
theorem pwFalse {α : Type} : ∀ l : List α, l.Pairwise (fun _ _ => False) → l.length ≤ 1
  | [], _ => by simp
  | [_], _ => by simp
  | _ :: b :: _, h => ((List.pairwise_cons.mp h).1 b (by simp)).elim

-- no permutation of [0, 1, 2] is sorted by rock-paper-scissors
theorem rpsKey : ∀ l : List (Fin 3), l.Perm [0, 1, 2] → ¬ l.Pairwise rps := by
  intro l hp
  have hl := hp.length_eq
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩ <;> simp at hl
  have key : ∀ a b c : Fin 3, [a, b, c].Perm [0, 1, 2] → ¬ [a, b, c].Pairwise rps := by decide
  exact key a b c hp
end query

section automata
open Cslib Cslib.Automata Cslib.Automata.NA

-- finite-word automata on Unit: empty language (all moves), {[]} (no moves), no start state
def naE : NA.FinAcc Unit Unit := { Tr := fun _ _ _ => True, start := Set.univ, accept := ∅ }
def naNil : NA.FinAcc Unit Unit := { Tr := fun _ _ _ => False, start := Set.univ, accept := Set.univ }
def naAll : NA.FinAcc Unit Unit := { Tr := fun _ _ _ => True, start := Set.univ, accept := Set.univ }
-- ω-automata: all moves / no start state on Unit; Bool: start false, every move goes to true
def nb : NA Unit Unit := { Tr := fun _ _ _ => True, start := Set.univ }
def nb0 : NA Unit Unit := { Tr := fun _ _ _ => True, start := ∅ }
def nbB : NA Bool Unit := { Tr := fun _ _ t => t = true, start := {false} }
def uS : ωSequence Unit := ⟨fun _ => ()⟩

theorem naE_lang (xs : List Unit) : xs ∉ Acceptor.language naE := by
  rintro ⟨_, _, _, h, _⟩; exact h
theorem naNil_nil : [] ∈ Acceptor.language naNil :=
  ⟨(), Set.mem_univ _, (), Set.mem_univ _, LTS.MTr.refl⟩
theorem naNil_cons (x : Unit) (xs : List Unit) : x :: xs ∉ Acceptor.language naNil := by
  rintro ⟨_, _, _, _, h⟩
  cases h with
  | stepL h _ => exact h

def naS0 : NA.FinAcc Unit Unit := { Tr := fun _ _ _ => True, start := ∅, accept := Set.univ }
-- accepts exactly the words of length one
def naB1 : NA.FinAcc Bool Unit := { Tr := fun s _ t => s = false ∧ t = true, start := {false}, accept := {true} }
def ssLR : ωSequence (Unit ⊕ Unit) := ⟨fun k => if k = 0 then .inl () else .inr ()⟩
def ssL : ωSequence (Unit ⊕ Unit) := ⟨fun _ => .inl ()⟩

theorem runLR : naE.loop.Run uS ssLR := by
  refine ⟨rfl, fun i => ?_⟩
  rcases i with _ | i
  · exact ⟨(), trivial, Set.mem_univ _⟩
  · exact (trivial : True)

theorem runL : naAll.loop.Run uS ssL := ⟨rfl, fun _ => ⟨(), (), trivial, Set.mem_univ _, Set.mem_univ _⟩⟩
def ssLB : ωSequence (Unit ⊕ Bool) := ⟨fun _ => .inl ()⟩
theorem runLB : naB1.loop.Run uS ssLB := ⟨rfl, fun _ => ⟨false, true, ⟨rfl, rfl⟩, rfl, rfl⟩⟩

theorem naB1_two (a b : Unit) : [a, b] ∉ Acceptor.language naB1 := by
  rintro ⟨s, hs, t, ht, h⟩
  cases h with
  | stepL h1 h2 =>
    cases h2 with
    | stepL h3 h4 =>
      simp only [naB1] at h1 h3
      rw [h1.2] at h3
      exact absurd h3.1 (by decide)

def εE : εNA.FinAcc Unit Unit := { Tr := fun _ _ _ => True, start := Set.univ, accept := ∅ }
def εN : εNA.FinAcc Unit Unit := { Tr := fun _ _ _ => False, start := ∅, accept := ∅ }

-- two-way automata on Unit: nothing (no start, no moves, nothing accepted); everything
def twN : TwoWayNA Unit Unit := { Tr := fun _ _ _ _ => False, start := ∅, accept := ∅ }
def twA : TwoWayNA Unit Unit := { Tr := fun _ _ _ _ => True, start := Set.univ, accept := Set.univ }
-- twA accepts the empty word
theorem twA_nil : Acceptor.Accepts twA [] :=
  ⟨[], ⟨[], (), 0⟩, ⟨Set.mem_univ _, rfl, rfl⟩, ⟨[], (), 0⟩, ⟨Set.mem_univ _, rfl⟩, LTS.MTr.refl⟩
-- an ε-transducer without transitions
def trN : NA.εTransducer Unit (Option Unit) (Option Unit) :=
  { Tr := fun _ _ _ => False, start := Set.univ, accept := Set.univ }
-- it translates nothing but the empty word
theorem trN_nil {xs : List (Option Unit)} {ys : List (Option Unit)} (h : trN.MTransl () xs ys ()) :
    xs = [] := by
  obtain ⟨μs, hm, hx, -⟩ := h
  cases hm with
  | refl => simpa [List.dropTaus] using hx.symm
  | stepL htr _ => exact htr.elim
end automata

section back
open Cslib Cslib.Automata Cslib.Automata.NA Acceptor

-- what a path of finLoop back to the hub says about its source state
def Back {State Symbol : Type*} (na : NA.FinAcc State Symbol) : Unit ⊕ Option State → List Symbol → Prop
  | .inl (), w => w = [] ∨ ∃ xs, xs ∈ language na
  | .inr (some u), _ => ∃ t ∈ na.accept, ∃ xs, na.MTr u xs t
  | .inr none, _ => False

theorem back {State Symbol : Type*} (na : NA.FinAcc State Symbol) {q : Unit ⊕ Option State}
    {w : List Symbol} {q' : Unit ⊕ Option State} (h : na.finLoop.MTr q w q') (hq : q' = .inl ()) :
    Back na q w := by
  induction h with
  | refl => subst hq; exact Or.inl rfl
  | @stepL q1 μ q2 μs q3 htr _ ih =>
    have ih := ih hq
    rcases q1 with ⟨⟩ | (_ | u) <;> rcases q2 with ⟨⟩ | (_ | v) <;>
      simp [FinAcc.finLoop, FinAcc.loop, NA.totalize, LTS.totalize, Back] at htr ih ⊢
    all_goals first
      | (obtain ⟨t, s, htr, hs, ht⟩ := htr; exact ⟨[μ], s, hs, t, ht, .stepL htr .refl⟩)
      | (obtain ⟨t, ht, xs, hm⟩ := ih; obtain ⟨s, htr, hs⟩ := htr
         exact ⟨μ :: xs, s, hs, t, ht, .stepL htr hm⟩)
      | (obtain ⟨t, htr, ht⟩ := htr; exact ⟨t, ht, [μ], .stepL htr .refl⟩)
      | (obtain ⟨t, ht, xs, hm⟩ := ih; exact ⟨t, ht, μ :: xs, .stepL htr hm⟩)
end back

section counter
open Cslib
-- the up/down counter LTS on ℕ: true increments, false decrements
def ctr : LTS ℕ Bool := ⟨fun s b t => if b then t = s + 1 else s = t + 1⟩

theorem ctr_inv {s : ℕ} {w : List Bool} {t : ℕ} (h : ctr.MTr s w t) :
    t + w.count false = s + w.count true := by
  induction h with
  | refl => simp
  | @stepL s1 μ s2 μs s3 htr _ ih =>
    cases μ <;> simp [ctr] at htr ⊢ <;> omega

theorem ctr_up (n s : ℕ) : ctr.MTr s (List.replicate n true) (s + n) := by
  induction n generalizing s with
  | zero => exact .refl
  | succ n ih =>
    have := ih (s + 1)
    rw [show s + 1 + n = s + (n + 1) by omega] at this
    exact .stepL (by simp [ctr]) this

theorem ctr_down (n s : ℕ) : ctr.MTr (s + n) (List.replicate n false) s := by
  induction n generalizing s with
  | zero => exact .refl
  | succ n ih =>
    have := ih s
    exact .stepL (show ctr.Tr (s + (n + 1)) false (s + n) by simp [ctr]; omega) this

theorem ctr_updown (n : ℕ) : ctr.MTr 0 (List.replicate n true ++ List.replicate n false) 0 := by
  have := LTS.MTr.comp ctr (ctr_up n 0) (ctr_down n 0)
  simpa using this

theorem ctr_count {m n : ℕ} (h : ctr.MTr 0 (List.replicate m true ++ List.replicate n false) 0) :
    m = n := by
  have := ctr_inv h
  simp [List.count_replicate] at this
  omega

-- a language containing trueⁿfalseⁿ but no trueᵐfalseⁿ with m ≠ n is not regular (Myhill–Nerode)
theorem notReg (l : Language Bool) (h1 : ∀ n, List.replicate n true ++ List.replicate n false ∈ l)
    (h2 : ∀ m n, List.replicate m true ++ List.replicate n false ∈ l → m = n) : ¬ l.IsRegular := by
  intro hr
  have := hr.finite_nerodeQuotient
  obtain ⟨m, n, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ => (⟦List.replicate k true⟧ : l.NerodeQuotient))
  have := (Quotient.eq.mp heq) (List.replicate n false)
  exact hne (h2 _ _ (this.mpr (h1 n)))

-- the successor Büchi automaton on ℕ accepting everywhere
def nbS : Cslib.Automata.NA.Buchi ℕ Unit := { Tr := fun s _ t => t = s + 1, start := {0}, accept := Set.univ }

theorem nbS_mtr {s : ℕ} {w : List Unit} {t : ℕ} (h : nbS.MTr s w t) : t = s + w.length := by
  induction h with
  | refl => simp
  | stepL htr _ ih => simp only [nbS] at htr; simp [ih, htr]; omega
end counter

end W1c0

section
open W1c0

-- `Cslib.Algorithms.Lean.TimeM.clog2_half_le` idx 1: removable (n = 0, 1: both sides 0)
theorem w1c0r0 : drop% Cslib.Algorithms.Lean.TimeM.clog2_half_le 1 := fun n => by
  rcases n with _ | _ | n
  · simp
  · simp
  · exact Cslib.Algorithms.Lean.TimeM.clog2_half_le _ (by omega)

-- `Cslib.Algorithms.Lean.TimeM.clog2_floor_half_le` idx 1: removable (n = 0, 1: both sides 0)
theorem w1c0r1 : drop% Cslib.Algorithms.Lean.TimeM.clog2_floor_half_le 1 := fun n => by
  rcases n with _ | _ | n
  · simp
  · simp
  · exact Cslib.Algorithms.Lean.TimeM.clog2_floor_half_le _ (by omega)

-- `Cslib.Query.gauss_le_naive` idx 8: necessary (c_add = 1, c_mul = 0)
theorem w1c0r2 : ¬ drop0% Cslib.Query.gauss_le_naive 8 := fun h => by
  have := h (α := ℕ) arOr 1 0 0 0 0 0
  rw [Cslib.Query.complexMulGauss_cost, Cslib.Query.complexMulNaive_cost] at this
  omega

-- `Cslib.Query.UpperBound.of_pointwise` idx 6: necessary (one query, bound 1 at size 0 and 0 above)
theorem w1c0r3 : ¬ drop0% Cslib.Query.UpperBound.of_pointwise 6 := fun h => by
  have := h (prog := fun _ : Unit => Cslib.Query.ArithQuery.doAdd (0 : ℕ) 0) (size := fun _ => 0)
    (bound := fun n => if n = 0 then 1 else 0) (fun o x => by simp [Cslib.FreeM.countQueries])
    arOr 1 () (by simp)
  simp [Cslib.FreeM.countQueries] at this

-- `Cslib.Query.UpperBound.of_pointwise` idx 7: necessary (one query, bound 0)
theorem w1c0r4 : ¬ drop0% Cslib.Query.UpperBound.of_pointwise 7 := fun h => by
  have := h (prog := fun _ : Unit => Cslib.Query.ArithQuery.doAdd (0 : ℕ) 0) (size := fun _ => 0)
    (bound := fun _ => 0) monotone_const arOr 0 () (by simp)
  exact absurd this (by decide)

-- `Cslib.Query.LowerBound.le_upperBound` idx 7: necessary (pure program, l = 1, u = 0)
theorem w1c0r5 : ¬ drop0% Cslib.Query.LowerBound.le_upperBound 7 := fun h => by
  have := h (prog := fun _ : Unit => (pure 0 : Cslib.FreeM (Cslib.Query.ArithQuery ℕ) ℕ)) (size := fun _ => 0)
    (l := fun _ => 1) (u := fun _ => 0) (fun _ _ _ _ => by simp) 0
  omega

-- `Cslib.Query.LowerBound.le_upperBound` idx 8: necessary (one query, l = 1, u = 0)
theorem w1c0r6 : ¬ drop0% Cslib.Query.LowerBound.le_upperBound 8 := fun h => by
  have := h (prog := fun _ : Unit => Cslib.Query.ArithQuery.doAdd (0 : ℕ) 0) (size := fun _ => 0)
    (l := fun _ => 1) (u := fun _ => 0) (fun n => ⟨(), by simp, arOr, Nat.le_of_eq rfl⟩) 0
  omega

-- `Cslib.Circuits.Synthesis.not` idx 4: necessary (NAND of two inputs needs two gates)
theorem w1c0r107 : ¬ drop0% Cslib.Circuits.Synthesis.not 4 := fun h => by
  obtain ⟨g, p, hg, -, ht⟩ := h (n := 2) (s := Cslib.Circuits.inputs 2) (a := 0)
    (f := fun x => x 0 && x 1) 0 .empty (Cslib.Circuits.inputs_subset_available _)
  exact nand2_no p (by omega) (ht rfl)

-- `Cslib.Circuits.Synthesis.and` idx 6: necessary (g = x0, f = ¬x1: x0 ∧ ¬x1 needs two gates)
theorem w1c0r108 : ¬ drop0% Cslib.Circuits.Synthesis.and 6 := fun h => by
  obtain ⟨g, p, hg, -, ht⟩ := h (n := 2) (s := Cslib.Circuits.inputs 2) (a := 0) (b := 0)
    (f := fun x => !x 1) (g := fun x => x 0) (Cslib.Circuits.Synthesis.of_mem ⟨0, rfl⟩)
    0 .empty (Cslib.Circuits.inputs_subset_available _)
  exact oneGate _ (by decide) (by decide) p (by omega) (ht rfl)

-- `Cslib.Circuits.Synthesis.and` idx 7: necessary (f = x0, g = ¬x1)
theorem w1c0r109 : ¬ drop0% Cslib.Circuits.Synthesis.and 7 := fun h => by
  obtain ⟨g, p, hg, -, ht⟩ := h (n := 2) (s := Cslib.Circuits.inputs 2) (a := 0) (b := 0)
    (f := fun x => x 0) (g := fun x => !x 1) (Cslib.Circuits.Synthesis.of_mem ⟨0, rfl⟩)
    0 .empty (Cslib.Circuits.inputs_subset_available _)
  exact oneGate _ (by decide) (by decide) p (by omega) (ht rfl)

-- `Cslib.Circuits.Synthesis.or` idx 6: necessary (g = x0, f = ¬x1)
theorem w1c0r110 : ¬ drop0% Cslib.Circuits.Synthesis.or 6 := fun h => by
  obtain ⟨g, p, hg, -, ht⟩ := h (n := 2) (s := Cslib.Circuits.inputs 2) (a := 0) (b := 0)
    (f := fun x => !x 1) (g := fun x => x 0) (Cslib.Circuits.Synthesis.of_mem ⟨0, rfl⟩)
    0 .empty (Cslib.Circuits.inputs_subset_available _)
  exact oneGate _ (by decide) (by decide) p (by omega) (ht rfl)

-- `Cslib.Circuits.Synthesis.or` idx 7: necessary (f = x0, g = ¬x1)
theorem w1c0r111 : ¬ drop0% Cslib.Circuits.Synthesis.or 7 := fun h => by
  obtain ⟨g, p, hg, -, ht⟩ := h (n := 2) (s := Cslib.Circuits.inputs 2) (a := 0) (b := 0)
    (f := fun x => x 0) (g := fun x => !x 1) (Cslib.Circuits.Synthesis.of_mem ⟨0, rfl⟩)
    0 .empty (Cslib.Circuits.inputs_subset_available _)
  exact oneGate _ (by decide) (by decide) p (by omega) (ht rfl)

-- `Cslib.Query.IsSort.perm` idx 2: necessary (sort returning [])
theorem w1c0r12 : ¬ drop0% Cslib.Query.IsSort.perm 2 := fun h => by
  have := h (sort := fun _ : List ℕ => pure []) [0] (leOr fun _ _ => true)
  simp at this

-- `Cslib.Query.IsSort.sorted` idx 2: necessary (identity sort on [1, 0] with ≤)
theorem w1c0r13 : ¬ drop0% Cslib.Query.IsSort.sorted 2 := fun h => by
  have := h (sort := fun xs : List ℕ => pure xs) [1, 0] (leOr fun a b => decide (a ≤ b)) (· ≤ ·)
    (fun _ _ => rfl)
  simp at this

-- `Cslib.Query.IsSort.sorted` idx 7: necessary (empty relation, merge sort on [0, 1])
theorem w1c0r14 : ¬ drop0% Cslib.Query.IsSort.sorted 7 := fun h => by
  have := @h ℕ _ Cslib.Query.mergeSort_isSort [0, 1] (leOr fun _ _ => false) (fun _ _ => False)
    (fun _ _ => instDecidableFalse) ⟨fun _ _ _ h _ => h⟩ (fun _ _ => rfl)
  have h2 := (Cslib.Query.mergeSort_isSort.perm [0, 1] (leOr fun _ _ => false)).length_eq
  have := pwFalse _ this
  simp only [List.length_cons, List.length_nil] at h2; omega

-- `Cslib.Query.IsSort.sorted` idx 8: necessary (rock-paper-scissors on Fin 3)
theorem w1c0r15 : ¬ drop0% Cslib.Query.IsSort.sorted 8 := fun h => by
  have := @h (Fin 3) _ Cslib.Query.mergeSort_isSort [0, 1, 2] (leOr fun a b => decide (rps a b)) rps
    _ _ (fun _ _ => rfl)
  have hp := List.mem_permutations.mpr (Cslib.Query.mergeSort_isSort.perm [0, 1, 2]
    (leOr fun a b => decide (rps a b)))
  exact rpsKey _ (List.mem_permutations.mp hp) this

-- `Cslib.Query.IsSort.sorted` idx 9: necessary (oracle answers ≥, relation ≤, input [1, 0])
theorem w1c0r16 : ¬ drop0% Cslib.Query.IsSort.sorted 9 := fun h => by
  have := @h ℕ _ Cslib.Query.mergeSort_isSort [1, 0] (leOr fun a b => decide (b ≤ a)) (· ≤ ·) _ _ _
  simp [Cslib.Query.eval_mergeSort, leOr] at this

-- `Cslib.Query.IsSort.eval_eq` idx 3: necessary (sort₁ returns [])
theorem w1c0r17 : ¬ drop0% Cslib.Query.IsSort.eval_eq 3 := fun h => by
  have := @h ℕ (fun _ => pure []) _ Cslib.Query.mergeSort_isSort (· ≤ ·) _ _ _ _
    (leOr fun a b => decide (a ≤ b)) (fun _ _ => rfl) [0]
  simp at this

-- `Cslib.Query.IsSort.eval_eq` idx 4: necessary (sort₂ returns [])
theorem w1c0r18 : ¬ drop0% Cslib.Query.IsSort.eval_eq 4 := fun h => by
  have := @h ℕ _ (fun _ => pure []) Cslib.Query.mergeSort_isSort (· ≤ ·) _ _ _ _
    (leOr fun a b => decide (a ≤ b)) (fun _ _ => rfl) [0]
  simp at this

-- `Cslib.Query.IsSort.eval_eq` idx 7: necessary (empty relation; merge sort vs merge sort of the reverse)
theorem w1c0r19 : ¬ drop0% Cslib.Query.IsSort.eval_eq 7 := fun h => by
  have := @h ℕ _ _ Cslib.Query.mergeSort_isSort revSort (fun _ _ => False)
    (fun _ _ => instDecidableFalse) ⟨fun _ _ _ h _ => h⟩ ⟨fun _ _ h _ => h.elim⟩
    (leOr fun _ _ => false) (fun _ _ => rfl) [0, 1]
  simp [leOr] at this

-- `Cslib.Query.IsSort.eval_eq` idx 9: necessary (full relation; merge sort vs merge sort of the reverse)
theorem w1c0r21 : ¬ drop0% Cslib.Query.IsSort.eval_eq 9 := fun h => by
  have := @h ℕ _ _ Cslib.Query.mergeSort_isSort revSort (fun _ _ => True)
    (fun _ _ => instDecidableTrue) ⟨fun _ _ => Or.inl trivial⟩ ⟨fun _ _ _ _ _ => trivial⟩
    (leOr fun _ _ => true) (fun _ _ => rfl) [0, 1]
  simp [leOr] at this

-- `Cslib.Query.IsSort.eval_eq` idx 11: necessary (oracle always true, relation ≤)
theorem w1c0r22 : ¬ drop0% Cslib.Query.IsSort.eval_eq 11 := fun h => by
  have := @h ℕ _ _ Cslib.Query.mergeSort_isSort revSort (· ≤ ·) _ _ _ _
    (leOr fun _ _ => true) [0, 1]
  simp [leOr] at this

-- `Cslib.Query.IsSort.lowerBound_infinite` idx 1: necessary (α = Empty: only [] with 0 queries)
theorem w1c0r29 : ¬ drop0% Cslib.Query.IsSort.lowerBound_infinite 1 := fun h => by
  obtain ⟨x, -, o, hx⟩ := @h Empty _ Cslib.Query.mergeSort_isSort 2
  rcases x with _ | ⟨a, _⟩
  · simp at hx; exact absurd hx (Nat.clog_pos (by norm_num) (by norm_num)).ne'
  · exact a.elim

-- `Cslib.Query.mergeSort_lowerBound` idx 1: necessary (α = Empty)
theorem w1c0r31 : ¬ drop0% Cslib.Query.mergeSort_lowerBound 1 := fun h => by
  obtain ⟨x, -, o, hx⟩ := @h Empty 2
  rcases x with _ | ⟨a, _⟩
  · simp at hx; exact absurd hx (Nat.clog_pos (by norm_num) (by norm_num)).ne'
  · exact a.elim

-- `Cslib.Query.IsSort.lowerBound_infinite` idx 3: necessary (sort returning [] at once)
theorem w1c0r30 : ¬ drop0% Cslib.Query.IsSort.lowerBound_infinite 3 := fun h => by
  obtain ⟨x, -, o, hx⟩ := @h ℕ _ (fun _ => pure []) 2
  simp at hx; exact absurd hx (Nat.clog_pos (by norm_num) (by norm_num)).ne'

-- `Cslib.Query.mergeSort_sorted` idx 3: necessary (empty relation)
theorem w1c0r32 : ¬ drop0% Cslib.Query.mergeSort_sorted 3 := fun h => by
  have := @h ℕ (fun _ _ => False) (fun _ _ => instDecidableFalse) ⟨fun _ _ _ h _ => h⟩
    (leOr fun _ _ => false) (fun _ _ => rfl) [0, 1]
  have h2 := (Cslib.Query.mergeSort_isSort.perm [0, 1] (leOr fun _ _ => false)).length_eq
  have := pwFalse _ this
  simp only [List.length_cons, List.length_nil] at h2; omega

-- `Cslib.Query.mergeSort_sorted` idx 4: necessary (rock-paper-scissors on Fin 3)
theorem w1c0r33 : ¬ drop0% Cslib.Query.mergeSort_sorted 4 := fun h => by
  have := @h (Fin 3) rps _ _ (leOr fun a b => decide (rps a b)) (fun _ _ => rfl) [0, 1, 2]
  have hp := List.mem_permutations.mpr (Cslib.Query.mergeSort_isSort.perm [0, 1, 2]
    (leOr fun a b => decide (rps a b)))
  exact rpsKey _ (List.mem_permutations.mp hp) this

-- `Cslib.Query.mergeSort_sorted` idx 6: necessary (oracle answers ≥, relation ≤)
theorem w1c0r34 : ¬ drop0% Cslib.Query.mergeSort_sorted 6 := fun h => by
  have := @h ℕ (· ≤ ·) _ _ _ (leOr fun a b => decide (b ≤ a)) [1, 0]
  simp [Cslib.Query.eval_mergeSort, leOr] at this

end

section
open W1c0

-- `Cslib.FreeM.exists_mem_countQueries_ge_clog` idx 7: necessary (S = ∅)
theorem w1c0r7 : ¬ drop0% _private.Cslib.Algorithms.Lean.Query.FreeM.«0».Cslib.FreeM.exists_mem_countQueries_ge_clog 7 := fun h => by
  obtain ⟨i, hi, -⟩ := @h Q0 Unit 2 (fun a => nomatch a) Unit (pure ()) ∅ (fun _ _ q => nomatch q)
    (by simp)
  simp at hi

-- `Cslib.FreeM.exists_mem_countQueries_ge_clog` idx 9: necessary (pure program, two oracles, r = 2)
theorem w1c0r8 : ¬ drop0% _private.Cslib.Algorithms.Lean.Query.FreeM.«0».Cslib.FreeM.exists_mem_countQueries_ge_clog 9 := fun h => by
  obtain ⟨i, hi, hc⟩ := @h Q0 Unit 2 (fun a => nomatch a) Bool (pure ()) Finset.univ
    Finset.univ_nonempty (fun _ _ q => nomatch q)
  simp at hc
  exact absurd hc (Nat.clog_pos (by norm_num) (by norm_num)).ne'

-- `Cslib.FreeM.exists_countQueries_ge_clog` idx 3: necessary (one query with 3 answers, r = 2)
theorem w1c0r9 : ¬ drop0% Cslib.FreeM.exists_countQueries_ge_clog 3 := fun h => by
  obtain ⟨i, hc⟩ := @h Q3 (Fin 3) 2 (Cslib.FreeM.lift .q) 3 (fun i => q3Or i) (by norm_num)
    (fun i j hij => by fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij (by decide))
  have h1 : Cslib.FreeM.countQueries (fun {ι} => q3Or i) (Cslib.FreeM.lift Q3.q) = 1 := rfl
  have h2 : Nat.clog 2 3 = 2 := by
    rw [Nat.clog_of_two_le (by norm_num) (by norm_num), Nat.clog_of_two_le (by norm_num) (by norm_num)]
    simp
  omega

-- `Cslib.FreeM.exists_countQueries_ge_clog` idx 7: necessary (n = 0)
theorem w1c0r10 : ¬ drop0% Cslib.FreeM.exists_countQueries_ge_clog 7 := fun h => by
  obtain ⟨i, -⟩ := @h Q0 Unit 2 (fun a => nomatch a) (pure ()) 0 (fun _ _ q => nomatch q)
    (fun i => i.elim0)
  exact i.elim0

-- `Cslib.FreeM.exists_countQueries_ge_clog` idx 8: necessary (pure program, two oracles, r = 2)
theorem w1c0r11 : ¬ drop0% Cslib.FreeM.exists_countQueries_ge_clog 8 := fun h => by
  obtain ⟨i, hc⟩ := @h Q0 Unit 2 (fun a => nomatch a) (pure ()) 2 (fun _ _ q => nomatch q) (by norm_num)
  simp at hc
  exact absurd hc (Nat.clog_pos (by norm_num) (by norm_num)).ne'

-- `Cslib.Query.instIsTransPrefixPermOrder` idx 3: necessary (n = 1, α = Empty)
theorem w1c0r23 : ¬ indep0% _private.Cslib.Algorithms.Lean.Query.Sort.LowerBound.«0».Cslib.Query.instIsTransPrefixPermOrder 3 := fun h => by
  have := @h 1 Empty 1; simp at this

-- `Cslib.Query.instTotalPrefixPermOrder` idx 3: necessary (n = 1, α = Empty)
theorem w1c0r24 : ¬ indep0% _private.Cslib.Algorithms.Lean.Query.Sort.LowerBound.«0».Cslib.Query.instTotalPrefixPermOrder 3 := fun h => by
  have := @h 1 Empty 1; simp at this

-- `Cslib.Query.instAntisymmPrefixPermOrder` idx 3: necessary (n = 1, α = Empty)
theorem w1c0r25 : ¬ indep0% _private.Cslib.Algorithms.Lean.Query.Sort.LowerBound.«0».Cslib.Query.instAntisymmPrefixPermOrder 3 := fun h => by
  have := @h 1 Empty 1; simp at this

-- `Cslib.Query.PrefixPermOrder_on_embedded` idx 3: necessary (n = 1, α = Empty)
theorem w1c0r26 : ¬ indep0% _private.Cslib.Algorithms.Lean.Query.Sort.LowerBound.«0».Cslib.Query.PrefixPermOrder_on_embedded 3 := fun h => by
  have := @h 1 Empty 1 0 0; simp at this

-- `Cslib.Query.pairwise_map_PrefixPermOrder` idx 2: necessary (n = 1, α = Empty)
theorem w1c0r27 : ¬ indep0% _private.Cslib.Algorithms.Lean.Query.Sort.LowerBound.«0».Cslib.Query.pairwise_map_PrefixPermOrder 2 := fun h => by
  have := @h 1 Empty 1; simp at this

-- `Cslib.Query.map_perm_of_finEmbedding` idx 2: necessary (n = 1, α = Empty)
theorem w1c0r28 : ¬ indep0% _private.Cslib.Algorithms.Lean.Query.Sort.LowerBound.«0».Cslib.Query.map_perm_of_finEmbedding 2 := fun h => by
  have := @h 1 Empty 1; simp at this

-- `Cslib.IsMonadHom.map_listInsertionSortM` idx 6: necessary (f = const none on Option, xs = [])
theorem w1c0r35 : ¬ drop0% Cslib.IsMonadHom.map_listInsertionSortM 6 := fun h => by
  have := @h ℕ Option Option _ _ (fun _ => none) (fun _ _ => some true) []
  simp at this

-- `Cslib.IsMonadHom.map_listMergeSortM` idx 6: necessary (f = const none on Option, xs = [])
theorem w1c0r37 : ¬ drop0% Cslib.IsMonadHom.map_listMergeSortM 6 := fun h => by
  have := @h Option Option _ _ ℕ (fun _ => none) [] (fun _ _ => some true)
  simp at this

-- `List.mergeM_pure` idx 3: necessary (bind-counting monad, merging [0] and [1])
theorem w1c0r36 : ¬ drop0% List.mergeM_pure 3 := fun h => by
  have := congrArg Prod.fst (@h (fun α => ℕ × α) cntM ℕ [0] [1] (fun a b => decide (a ≤ b)))
  simp at this

end

section
open W1c0 Cslib Cslib.Automata Cslib.Automata.NA

-- `Cslib.Automata.NA.concat_start_right` idx 7: necessary (no run needed; empty na1 language)
theorem w1c0r47 : ¬ drop0% Cslib.Automata.NA.concat_start_right 7 := fun h =>
  naE_lang _ (h (na1 := naE) (na2 := nb) (xs := uS) (ss := ⟨fun _ => .inr ()⟩) rfl)

-- `Cslib.Automata.NA.concat_start_right` idx 8: necessary (run staying left, empty na1 language)
theorem w1c0r48 : ¬ drop0% Cslib.Automata.NA.concat_start_right 8 := fun h =>
  naE_lang _ (h (na1 := naE) (na2 := nb) (xs := uS) (ss := ⟨fun _ => .inl ()⟩)
    ⟨Set.mem_union_left _ ⟨(), Set.mem_univ _, rfl⟩, fun _ => trivial⟩)

-- `Cslib.Automata.NA.concat_run_left` idx 7: necessary (na1 without start states)
theorem w1c0r49 : ¬ drop0% Cslib.Automata.NA.concat_run_left 7 := fun h => by
  obtain ⟨s1, t1, -, hs, -⟩ := h (na1 := { naAll with start := ∅ }) (na2 := nb) (xs := uS)
    (ss := ⟨fun _ => .inl ()⟩) 0 (fun _ _ => rfl)
  exact hs

-- `Cslib.Automata.NA.concat_run_left` idx 9: necessary (run starting right since na1 accepts [])
theorem w1c0r50 : ¬ drop0% Cslib.Automata.NA.concat_run_left 9 := fun h => by
  obtain ⟨s1, t1, -, -, h0, -⟩ := h (na1 := naNil) (na2 := nb) (xs := uS)
    (ss := ⟨fun _ => .inr ()⟩) ⟨Set.mem_union_right _ ⟨naNil_nil, (), Set.mem_univ _, rfl⟩,
      fun _ => trivial⟩ 0
  cases h0

-- `Cslib.Automata.NA.concat_run_left_right` idx 7: necessary (no run; empty na1 language)
theorem w1c0r51 : ¬ drop0% Cslib.Automata.NA.concat_run_left_right 7 := fun h =>
  naE_lang _ (h (na1 := naE) (na2 := nb) (xs := uS)
    (ss := ⟨fun k => if k = 0 then .inl () else .inr ()⟩) 1 (by norm_num)
    (fun k hk => by obtain rfl : k = 0 := by omega
                    rfl) rfl)

-- `Cslib.Automata.NA.concat_run_left_right` idx 9: removable (n = 0: the run starts right, so na1 accepts [])
theorem w1c0r52 : drop% Cslib.Automata.NA.concat_run_left_right 9 := by
  intro Symbol State1 State2 na1 na2 xs ss hc n hl hr
  rcases n with _ | n
  · exact Cslib.Automata.NA.concat_start_right hc hr
  · exact Cslib.Automata.NA.concat_run_left_right hc _ (by omega) hl hr

-- `Cslib.Automata.NA.concat_run_left_right` idx 10: necessary (na1 accepts only []; run right from the start)
theorem w1c0r53 : ¬ drop0% Cslib.Automata.NA.concat_run_left_right 10 := fun h =>
  naNil_cons _ _ (h (na1 := naNil) (na2 := nb) (xs := uS) (ss := ⟨fun _ => .inr ()⟩)
    ⟨Set.mem_union_right _ ⟨naNil_nil, (), Set.mem_univ _, rfl⟩, fun _ => trivial⟩ 1 (by norm_num) rfl)

-- `Cslib.Automata.NA.concat_run_left_right` idx 11: necessary (run staying left; empty na1 language)
theorem w1c0r54 : ¬ drop0% Cslib.Automata.NA.concat_run_left_right 11 := fun h =>
  naE_lang _ (h (na1 := naE) (na2 := nb) (xs := uS) (ss := ⟨fun _ => .inl ()⟩)
    ⟨Set.mem_union_left _ ⟨(), Set.mem_univ _, rfl⟩, fun _ => trivial⟩ 1 (by norm_num) (fun _ _ => rfl))

-- `Cslib.Automata.NA.concat_run_right` idx 7: necessary (na2 without start states)
theorem w1c0r55 : ¬ drop0% Cslib.Automata.NA.concat_run_right 7 := fun h => by
  obtain ⟨ss2, hr, -⟩ := h (na1 := naE) (na2 := nb0) (xs := uS) (ss := ⟨fun _ => .inr ()⟩) 0
    (fun _ h => absurd h (Nat.not_lt_zero _)) rfl
  exact hr.start

-- `Cslib.Automata.NA.concat_run_right` idx 9: necessary (na2 on Bool starts at false, then true forever; n = 1)
theorem w1c0r56 : ¬ drop0% Cslib.Automata.NA.concat_run_right 9 := fun h => by
  obtain ⟨ss2, hr, he⟩ := h (na1 := naNil) (na2 := nbB) (xs := uS)
    (ss := ⟨fun k => .inr (decide (0 < k))⟩)
    ⟨Set.mem_union_right _ ⟨naNil_nil, false, rfl, rfl⟩, fun i => by simp [concat, nbB]⟩ 1 rfl
  have h1 := hr.start
  have h2 := congrArg (fun s : ωSequence (Unit ⊕ Bool) => s 0) he
  simp [nbB] at h1
  simp [ωSequence.drop, h1] at h2

-- `Cslib.Automata.NA.concat_run_right` idx 10: necessary (run staying left, n = 0)
theorem w1c0r57 : ¬ drop0% Cslib.Automata.NA.concat_run_right 10 := fun h => by
  obtain ⟨ss2, hr, he⟩ := h (na1 := naE) (na2 := nb) (xs := uS) (ss := ⟨fun _ => .inl ()⟩)
    ⟨Set.mem_union_left _ ⟨(), Set.mem_univ _, rfl⟩, fun _ => trivial⟩ 0
    (fun _ h => absurd h (Nat.not_lt_zero _))
  have h2 := congrArg (fun s : ωSequence (Unit ⊕ Unit) => s 0) he
  simp [ωSequence.drop] at h2

-- `Cslib.Automata.NA.concat_run_proj` idx 8: necessary (no run; empty na1 language, k = 0)
theorem w1c0r58 : ¬ drop0% Cslib.Automata.NA.concat_run_proj 8 := fun h => by
  obtain ⟨n, -, hn, -⟩ := h (na1 := naE) (na2 := nb) (xs := uS) (ss := ⟨fun _ => .inr ()⟩) (k := 0) rfl
  exact naE_lang _ hn

-- `Cslib.Automata.NA.concat_run_proj` idx 9: necessary (run staying left; empty na1 language)
theorem w1c0r59 : ¬ drop0% Cslib.Automata.NA.concat_run_proj 9 := fun h => by
  obtain ⟨n, -, hn, -⟩ := h (na1 := naE) (na2 := nb) (xs := uS) (ss := ⟨fun _ => .inl ()⟩) (k := 0)
    ⟨Set.mem_union_left _ ⟨(), Set.mem_univ _, rfl⟩, fun _ => trivial⟩
  exact naE_lang _ hn

-- `Cslib.Automata.NA.concat_run_exists` idx 8: necessary (empty na1 language, xs1 = [])
theorem w1c0r60 : ¬ drop0% Cslib.Automata.NA.concat_run_exists 8 := fun h => by
  obtain ⟨ss, hr, he⟩ := h (na1 := naE) (na2 := nb) (xs1 := []) (xs2 := uS) (ss2 := ⟨fun _ => ()⟩)
    ⟨Set.mem_univ _, fun _ => trivial⟩
  have h2 := congrArg (fun s : ωSequence (Unit ⊕ Unit) => s 0) he
  have h1 := hr.start
  simp [ωSequence.drop] at h2
  simp [concat, h2] at h1
  exact naE_lang _ h1.1

-- `Cslib.Automata.NA.concat_run_exists` idx 9: necessary (na2 without start states, xs1 = [])
theorem w1c0r61 : ¬ drop0% Cslib.Automata.NA.concat_run_exists 9 := fun h => by
  obtain ⟨ss, hr, he⟩ := h (na1 := naNil) (na2 := nb0) (xs1 := []) (xs2 := uS) (ss2 := ⟨fun _ => ()⟩)
    naNil_nil
  have h2 := congrArg (fun s : ωSequence (Unit ⊕ Unit) => s 0) he
  have h1 := hr.start
  simp [ωSequence.drop] at h2
  simp [concat, h2, nb0] at h1

end

section
open W1c0 Cslib Cslib.Automata Cslib.Automata.NA

-- `Cslib.Automata.NA.loop_run_left_left` idx 5: necessary (no run; empty language)
theorem w1c0r65 : ¬ drop0% Cslib.Automata.NA.loop_run_left_left 5 := fun h =>
  naE_lang _ (h (na := naE) (xs := uS) (ss := ssL) rfl)

-- `Cslib.Automata.NA.loop_run_left_left` idx 6: necessary (run going right; empty language)
theorem w1c0r66 : ¬ drop0% Cslib.Automata.NA.loop_run_left_left 6 := fun h =>
  naE_lang _ (h (na := naE) (xs := uS) (ss := ssLR) runLR)

-- `Cslib.Automata.NA.loop_run_left_right` idx 5: necessary (no start states, no run)
theorem w1c0r67 : ¬ drop0% Cslib.Automata.NA.loop_run_left_right 5 := fun h => by
  obtain ⟨s, t, -, hs, -⟩ := h (na := naS0) (xs := uS) (ss := ssLR) 1 (by norm_num)
    (fun k hk _ => by
      show (if k = 0 then _ else _ : Unit ⊕ Unit).isRight = true
      split <;> first | omega | rfl)
  exact hs

-- `Cslib.Automata.NA.loop_run_left_right` idx 7: necessary (n = 0; the run starts left)
theorem w1c0r68 : ¬ drop0% Cslib.Automata.NA.loop_run_left_right 7 := fun h => by
  obtain ⟨s, t, -, -, h0⟩ := h (na := naAll) (xs := uS) (ss := ssL) runL 0 (fun _ _ _ => by omega)
  cases h0

-- `Cslib.Automata.NA.loop_run_left_right` idx 8: necessary (run staying left, n = 1)
theorem w1c0r69 : ¬ drop0% Cslib.Automata.NA.loop_run_left_right 8 := fun h => by
  obtain ⟨s, t, -, -, h0⟩ := h (na := naAll) (xs := uS) (ss := ssL) runL 1 (by norm_num)
  cases h0

-- `Cslib.Automata.NA.loop_run_left_right_left` idx 5: necessary (no run; empty language)
theorem w1c0r70 : ¬ drop0% Cslib.Automata.NA.loop_run_left_right_left 5 := fun h =>
  naE_lang _ (h (na := naE) (xs := uS) (ss := ssL) 1 ⟨by norm_num, rfl⟩ (fun _ _ _ => by omega))

-- `Cslib.Automata.NA.loop_run_left_right_left` idx 7: necessary (n = 0: [] not accepted)
theorem w1c0r71 : ¬ drop0% Cslib.Automata.NA.loop_run_left_right_left 7 := fun h =>
  naE_lang _ (h (na := naE) (xs := uS) (ss := ssLR) runLR 0 (fun _ _ _ => by omega))

-- `Cslib.Automata.NA.loop_run_left_right_left` idx 8: necessary (na accepts only length-1 words; n = 2)
theorem w1c0r72 : ¬ drop0% Cslib.Automata.NA.loop_run_left_right_left 8 := fun h =>
  naB1_two _ _ (h (na := naB1) (xs := uS) (ss := ssLB) runLB 2 ⟨by norm_num, rfl⟩)

-- `Cslib.Automata.NA.loop_run_from_left` idx 5: necessary (n = 0, constant left sequence is no run)
theorem w1c0r73 : ¬ drop0% Cslib.Automata.NA.loop_run_from_left 5 := fun h => by
  have := (h (na := naE) (xs := uS) (ss := ssL) 0 rfl).trans 0
  obtain ⟨_, _, _, _, h⟩ := this
  exact h

-- `Cslib.Automata.NA.loop_run_from_left` idx 7: necessary (n = 1 is right, not a start state)
theorem w1c0r74 : ¬ drop0% Cslib.Automata.NA.loop_run_from_left 7 := fun h => by
  have := (h (na := naE) (xs := uS) (ss := ssLR) runLR 1).start
  simp [ssLR, ωSequence.drop, FinAcc.loop] at this

-- `Cslib.Automata.NA.loop_run_one_iter` idx 6: necessary (no run; empty language)
theorem w1c0r75 : ¬ drop0% Cslib.Automata.NA.loop_run_one_iter 6 := fun h => by
  obtain ⟨n, -, hn, -⟩ := h (na := naE) (xs := uS) (ss := ssL) (k := 1) (by norm_num) rfl
  exact naE_lang _ hn.1

-- `Cslib.Automata.NA.loop_run_one_iter` idx 7: necessary (k = 0: [] is excluded)
theorem w1c0r76 : ¬ drop0% Cslib.Automata.NA.loop_run_one_iter 7 := fun h => by
  obtain ⟨n, hn0, hn, -⟩ := h (na := naAll) (xs := uS) (ss := ssL) (k := 0) runL rfl
  obtain rfl : n = 0 := by omega
  exact hn.2 rfl

-- `Cslib.Automata.NA.loop_run_one_iter` idx 8: necessary (run going right; empty language)
theorem w1c0r77 : ¬ drop0% Cslib.Automata.NA.loop_run_one_iter 8 := fun h => by
  obtain ⟨n, -, hn, -⟩ := h (na := naE) (xs := uS) (ss := ssLR) (k := 1) runLR (by norm_num)
  exact naE_lang _ hn.1

-- `Cslib.Automata.NA.loop_fin_run_mtr` idx 4: necessary (empty language, xl = [()])
theorem w1c0r79 : ¬ drop0% Cslib.Automata.NA.loop_fin_run_mtr 4 := fun h => by
  have := h (na := naE) (xl := [()])
  cases this with
  | stepL h1 h2 =>
    cases h2
    obtain ⟨_, _, _, _, h⟩ := h1
    exact h

-- `Cslib.Automata.NA.loop_fin_run_exists` idx 4: necessary (empty language, xl = [()])
theorem w1c0r78 : ¬ drop0% Cslib.Automata.NA.loop_fin_run_exists 4 := fun h => by
  obtain ⟨sl, hl, h0, h1, ht⟩ := h (na := naE) (xl := [()])
  have := ht 0 (by simp)
  match sl, hl, h0, h1, this with
  | [a, b], _, h0, h1, this =>
    simp only [List.getElem_cons_zero, List.length_cons, List.length_nil, zero_add,
      List.getElem_cons_succ] at h0 h1 this
    subst h0 h1
    obtain ⟨_, _, _, _, h⟩ := this
    exact h

-- `Cslib.Automata.NA.loop_run_exists` idx 5: necessary (empty language, words [()])
theorem w1c0r80 : ¬ drop0% Cslib.Automata.NA.loop_run_exists 5 := fun h => by
  obtain ⟨ss, hr, hc⟩ := h (na := naE) (xls := ⟨fun _ => [()]⟩)
  have h0 := hc 0
  have h1 := hc 1
  simp [ωSequence.cumLen] at h0 h1
  have := hr.trans 0
  rw [h0, h1] at this
  obtain ⟨_, _, _, _, h⟩ := this
  exact h

-- `Cslib.Automata.NA.FinAcc.instTotalSumUnitOptionFinLoopOfNonemptyElemStart` idx 3: necessary (no start states)
theorem w1c0r81 : ¬ drop0% Cslib.Automata.NA.FinAcc.instTotalSumUnitOptionFinLoopOfNonemptyElemStart 3 := fun h => by
  obtain ⟨t, ht⟩ := (h (na := naS0)).total (.inl ()) ()
  rcases t with ⟨⟩ | t <;> simp [FinAcc.finLoop, FinAcc.loop, NA.totalize, naS0] at ht

-- `Cslib.Automata.NA.totalize_mtr_run` idx 7: necessary (no start states, xl = [])
theorem w1c0r86 : ¬ drop0% Cslib.Automata.NA.totalize_mtr_run 7 := fun h => by
  obtain ⟨xs, ss, hr, h0, -⟩ := h (na := nb0) (xl := []) (s := ()) (t := ()) LTS.MTr.refl
  have := hr.start
  rw [h0] at this
  simp [NA.totalize, nb0] at this

-- `Cslib.Automata.NA.totalize_mtr_run` idx 8: necessary (no transitions, xl = [()])
theorem w1c0r87 : ¬ drop0% Cslib.Automata.NA.totalize_mtr_run 8 := fun h => by
  obtain ⟨xs, ss, hr, h0, h1⟩ := h (na := { nb with Tr := fun _ _ _ => False }) (xl := [()])
    (s := ()) (t := ()) (Set.mem_univ _)
  have := hr.trans 0
  simp only [List.length_cons, List.length_nil, zero_add] at h1
  rw [h0, h1] at this
  exact this

end

section
open W1c0 Cslib Cslib.Automata Cslib.Automata.NA Cslib.Automata.NA.Buchi Filter

-- `Cslib.Automata.εNA.FinAcc.reduceOption_mem_kstar_of_star_mTr` idx 4: necessary (empty language, μs = [some ()])
theorem w1c0r38 : ¬ drop0% Cslib.Automata.εNA.FinAcc.reduceOption_mem_kstar_of_star_mTr 4 := fun h => by
  have := h (a := εE) (μs := [some ()])
  obtain ⟨L, hL, hm⟩ := Language.mem_kstar.mp this
  rcases L with _ | ⟨w, L⟩
  · simp at hL
  · obtain ⟨_, _, _, ht, _⟩ := εNA.FinAcc.mem_language_iff.mp (hm w (by simp))
    exact ht

-- `Cslib.Automata.εNA.FinAcc.exists_star_mTr_of_mem_kstar` idx 4: necessary (no start states, xs = [()])
theorem w1c0r39 : ¬ drop0% Cslib.Automata.εNA.FinAcc.exists_star_mTr_of_mem_kstar 4 := fun h => by
  obtain ⟨μs, hred, hm⟩ := h (a := εN) (xs := [()])
  cases hm with
  | refl => simp at hred
  | stepL htr _ =>
    cases htr with
    | enter hs => exact hs

-- `Cslib.Automata.εNA.FinAcc.toSingleStartAccept_tr_inl_false` idx 5: necessary (μ = some ())
theorem w1c0r40 : ¬ drop0% Cslib.Automata.εNA.FinAcc.toSingleStartAccept_tr_inl_false 5 := fun h => by
  have := (h (a := εE) (μ := some ()) (y := .inl true)).1
  cases this

-- `Cslib.Automata.NA.Run.trans` idx 5: necessary (no transitions)
theorem w1c0r41 : ¬ drop0% Cslib.Automata.NA.Run.trans 5 := fun h =>
  h (na := ({ Tr := fun _ _ _ => False, start := Set.univ } : NA Unit Unit)) (xs := uS) (ss := uS) 0

-- `Cslib.Automata.NA.Buchi.inter_freq_acc_freq_acc` idx 7: necessary (no run; history bit stays false)
theorem w1c0r42 : ¬ drop0% Cslib.Automata.NA.Buchi.inter_freq_acc_freq_acc 7 := fun h => by
  have := h (State := fun _ => Unit) (Symbol := Unit) (na := fun _ => nb) (acc := fun _ => Set.univ)
    (xs := uS) (ss := ⟨fun _ => (fun _ => (), false)⟩) (i := false)
    (Eventually.frequently (Eventually.of_forall fun k => ⟨Set.mem_univ _, rfl⟩))
  obtain ⟨k, hk⟩ := this.exists
  simp [interAcc] at hk

-- `Cslib.Automata.NA.Buchi.inter_freq_acc_freq_acc` idx 8: necessary (empty acceptance sets)
theorem w1c0r43 : ¬ drop0% Cslib.Automata.NA.Buchi.inter_freq_acc_freq_acc 8 := fun h => by
  have := h (State := fun _ => Unit) (Symbol := Unit) (na := fun _ => nb) (acc := fun _ => ∅)
    (xs := uS) (ss := ⟨fun _ => (fun _ => (), false)⟩) (i := false)
    ⟨⟨by simp [NA.iProd, nb], rfl⟩, fun k => ⟨fun _ => trivial, by simp [histTrans, interAcc]⟩⟩
  obtain ⟨k, hk⟩ := this.exists
  simp [interAcc] at hk

-- `Cslib.Automata.NA.Buchi.inter_freq_comp_acc_freq_acc` idx 6: necessary (components accept alternately, history bit out of phase)
theorem w1c0r44 : ¬ drop0% Cslib.Automata.NA.Buchi.inter_freq_comp_acc_freq_acc 6 := fun h => by
  have := h (State := fun _ => Bool) (Symbol := Unit) (na := fun _ => { Tr := fun _ _ _ => True, start := Set.univ })
    (acc := fun _ => {true}) (xs := uS)
    (ss := ⟨fun k => (fun i => i != decide (k % 2 = 0), decide (k % 2 = 0))⟩)
    (frequently_atTop.mpr fun N => ⟨2 * N, by omega, by simp⟩)
    (frequently_atTop.mpr fun N => ⟨2 * N + 1, by omega, by simp [Nat.add_mod]⟩)
  obtain ⟨k, hk⟩ := this.exists
  simp [interAccept, interAcc] at hk
  omega

-- `Cslib.Automata.NA.Buchi.inter_freq_comp_acc_freq_acc` idx 7: necessary (component false never accepts)
theorem w1c0r45 : ¬ drop0% Cslib.Automata.NA.Buchi.inter_freq_comp_acc_freq_acc 7 := fun h => by
  have := h (State := fun _ => Unit) (Symbol := Unit) (na := fun _ => nb) (acc := fun i => {_u | i = true})
    (xs := uS) (ss := ⟨fun _ => (fun _ => (), false)⟩)
    ⟨⟨by simp [NA.iProd, nb], rfl⟩, fun k => ⟨fun _ => trivial, by simp [histTrans, interAcc]⟩⟩
    (Eventually.frequently (Eventually.of_forall fun k => rfl))
  obtain ⟨k, hk⟩ := this.exists
  simp [interAccept, interAcc] at hk

-- `Cslib.Automata.NA.Buchi.inter_freq_comp_acc_freq_acc` idx 8: necessary (component true never accepts; history bit true from step 1)
theorem w1c0r46 : ¬ drop0% Cslib.Automata.NA.Buchi.inter_freq_comp_acc_freq_acc 8 := fun h => by
  have := h (State := fun _ => Unit) (Symbol := Unit) (na := fun _ => nb) (acc := fun i => {_u | i = false})
    (xs := uS) (ss := ⟨fun k => (fun _ => (), decide (0 < k))⟩)
    ⟨⟨by simp [NA.iProd, nb], rfl⟩, fun k => ⟨fun _ => trivial, by
      rcases k with _ | k <;> simp [histTrans, interAcc]⟩⟩
    (Eventually.frequently (Eventually.of_forall fun k => rfl))
  obtain ⟨k, hk, hm⟩ := frequently_atTop.mp this 1
  simp [interAccept, interAcc] at hm
  omega

-- `Cslib.Automata.NA.hist_run_exists` idx 8: necessary (no start states)
theorem w1c0r64 : ¬ drop0% Cslib.Automata.NA.hist_run_exists 8 := fun h => by
  obtain ⟨ss', hr, -⟩ := h (na := nb0) (start' := fun _ => ()) (tr' := fun _ _ _ => ()) (xs := uS) (ss := uS)
  exact (NA.hist_run_proj hr).start

end

section
open W1c0 Cslib Cslib.Automata Cslib.Automata.NA

-- `Cslib.Automata.TwoWayNACfg.ext` idx 4: necessary (inputs [true], [false] of equal length)
theorem w1c0r88 : ¬ drop0% Cslib.Automata.TwoWayNACfg.ext 4 := fun h => by
  have := congrArg TwoWayNACfg.input (h (x := (⟨[true], (), 0⟩ : TwoWayNACfg Unit Bool))
    (y := ⟨[false], (), 0⟩) rfl HEq.rfl)
  simp at this

-- `Cslib.Automata.TwoWayNACfg.ext` idx 5: necessary (states false, true)
theorem w1c0r89 : ¬ drop0% Cslib.Automata.TwoWayNACfg.ext 5 := fun h => by
  have := congrArg TwoWayNACfg.state (h (x := (⟨[], false, 0⟩ : TwoWayNACfg Bool Unit))
    (y := ⟨[], true, 0⟩) rfl HEq.rfl)
  simp at this

-- `Cslib.Automata.TwoWayNACfg.ext` idx 6: necessary (positions 0, 1 on input [()])
theorem w1c0r90 : ¬ drop0% Cslib.Automata.TwoWayNACfg.ext 6 := fun h => by
  have := congrArg (fun c => (c.pos : ℕ)) (h (x := (⟨[()], (), 0⟩ : TwoWayNACfg Unit Unit))
    (y := ⟨[()], (), 1⟩) rfl rfl)
  simp at this

-- `Cslib.Automata.TwoWayNACfg.eta` idx 4: necessary (c on [()], input [])
theorem w1c0r91 : ¬ drop0% Cslib.Automata.TwoWayNACfg.eta 4 := fun h => by
  have := congrArg TwoWayNACfg.input (h (input := ([] : List Unit))
    (c := (⟨[()], (), 0⟩ : TwoWayNACfg Unit Unit)) (by simp))
  simp at this

-- `Cslib.Automata.TwoWayNA.getElem_of_tr` idx 8: necessary (empty input: head not inside)
theorem w1c0r92 : ¬ drop0% Cslib.Automata.TwoWayNA.getElem_of_tr 8 := fun h => by
  obtain ⟨hl, -⟩ := h (a := twA) (input := []) (c := ⟨[], (), 0⟩) (c' := ⟨[], (), 0⟩) (x := ())
    (m := 0) rfl
  simp at hl

-- `Cslib.Automata.TwoWayNA.getElem_of_tr` idx 9: necessary (step on [()] while input = [])
theorem w1c0r93 : ¬ drop0% Cslib.Automata.TwoWayNA.getElem_of_tr 9 := fun h => by
  obtain ⟨hl, -⟩ := h (a := twA) (input := []) (c := ⟨[()], (), 0⟩) (c' := ⟨[()], (), 1⟩) (x := ())
    (m := 1) ⟨rfl, rfl, trivial, by simp⟩
  simp at hl

-- `Cslib.Automata.TwoWayNA.IsRejectionCert.start_mem` idx 7: necessary (empty certificate)
theorem w1c0r94 : ¬ drop0% Cslib.Automata.TwoWayNA.IsRejectionCert.start_mem 7 := fun h =>
  h (a := twN) (input := []) (cert := ⟨fun _ => ∅⟩)
    ⟨fun _ hs => hs, fun _ _ _ ht _ => ht.2.2.1.elim, fun _ hs => hs.elim⟩ () 

-- `Cslib.Automata.TwoWayNA.IsRejectionCert.step_closed` idx 5: necessary (all moves; certificate univ at 0 only)
theorem w1c0r95 : ¬ drop0% Cslib.Automata.TwoWayNA.IsRejectionCert.step_closed 5 := fun h => by
  have := h (a := twA) (input := [()]) (cert := ⟨fun i => {_u | i = 0}⟩) ⟨[()], (), 0⟩ ((), 1)
    ⟨[()], (), 1⟩ ⟨rfl, rfl, trivial, by simp⟩ ⟨rfl, rfl⟩
  simp at this

-- `Cslib.Automata.TwoWayNA.IsRejectionCert.accept_notMem` idx 7: necessary (every state accepting, empty certificate)
theorem w1c0r96 : ¬ drop0% Cslib.Automata.TwoWayNA.IsRejectionCert.accept_notMem 7 := fun h =>
  h (a := { twN with accept := Set.univ }) (input := []) (cert := ⟨fun _ => ∅⟩)
    ⟨fun _ hs => hs, fun _ _ _ ht _ => ht.2.2.1.elim, fun _ hs => hs.elim⟩ () (Set.mem_univ _)

-- `Cslib.Automata.TwoWayNA.IsRejectionCert.not_accepts` idx 5: necessary (automaton accepting [])
theorem w1c0r97 : ¬ drop0% Cslib.Automata.TwoWayNA.IsRejectionCert.not_accepts 5 := fun h =>
  h (a := twA) (input := []) (cert := ⟨fun _ => ∅⟩) twA_nil

-- `Cslib.Automata.TwoWayNA.isRejectionCert_reachable` idx 4: necessary (automaton accepting [])
theorem w1c0r98 : ¬ drop0% Cslib.Automata.TwoWayNA.isRejectionCert_reachable 4 := fun h =>
  (h (a := twA) (input := [])).not_accepts twA_nil

-- `Cslib.Automata.TwoWayNA.mTr_take_of_mTr_toCfgNA` idx 7: necessary (non-initial configuration at position 1)
theorem w1c0r99 : ¬ drop0% Cslib.Automata.TwoWayNA.mTr_take_of_mTr_toCfgNA 7 := fun h => by
  have := h (a := naNil) (input := [()]) (c := ⟨[()], (), 1⟩) (c' := ⟨[()], (), 1⟩) (μs := []) .refl
  cases this with
  | stepL h1 _ => exact h1

-- `Cslib.Automata.TwoWayNA.mTr_toCfgNA_of_mTr` idx 8: necessary (no transitions, pre = input = [()])
theorem w1c0r100 : ¬ drop0% Cslib.Automata.TwoWayNA.mTr_toCfgNA_of_mTr 8 := fun h => by
  have := h (a := naNil) (input := [()]) (s := ()) (s' := ()) (pre := [()]) (List.prefix_refl _)
  cases this with
  | stepL h1 _ => exact h1.2.2.1.2

end

section
open W1c0

-- `Cslib.Circuits.Boolean.Lupanov.error_le` idx 3: removable (if 3 log₂ n > n then n ≤ 8, the exponent is 0 and c ≤ 1)
theorem w1c0r101 : drop% _private.Cslib.Computability.Circuit.Boolean.Lupanov.«0».Cslib.Circuits.Boolean.Lupanov.error_le 3 := by
  intro c n hc
  by_cases hn : 3 * Nat.log2 n ≤ n
  · exact (priv% _private.Cslib.Computability.Circuit.Boolean.Lupanov.«0».Cslib.Circuits.Boolean.Lupanov.error_le) c n hc hn
  · have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    have h2 := Nat.log2_self_le hn0
    have hk : Nat.log2 n < 4 := by
      by_contra hk
      have := three_mul_le_two_pow (Nat.log2 n) (by omega)
      omega
    have h8 : n ≤ 8 := by omega
    have hc1 : c ≤ 1 := by omega
    rw [Nat.sub_eq_zero_of_le (by omega), pow_zero, mul_one]
    interval_cases n <;> interval_cases c <;> omega

-- `Cslib.Circuits.Boolean.Lupanov.exists_circuit_of_split` idx 4: necessary (k = d = 0, s = 1: bound 29, but hard functions exist)
theorem w1c0r102 : ¬ drop0% _private.Cslib.Computability.Circuit.Boolean.Lupanov.«0».Cslib.Circuits.Boolean.Lupanov.exists_circuit_of_split 4 := fun h => by
  obtain ⟨N, hN⟩ := Cslib.Circuits.Boolean.Shannon.exists_hard_function
  obtain ⟨f, hf⟩ := hN (max N 10) (le_max_left _ _)
  obtain ⟨c, hc, hs⟩ := h (n := max N 10) (k := 0) (d := 0) (s := 1) (by norm_num) f
  have hlt := hf c hc
  have hb : Cslib.Circuits.Boolean.Lupanov.bound 0 0 1 = 29 := by decide
  rw [hb] at hs
  have h29 := t29 (max N 10) (le_max_right _ _)
  have hpos : (0 : ℝ) < (max N 10 : ℕ) := by exact_mod_cast (by omega : 0 < max N 10)
  rw [div_lt_iff₀ hpos] at hlt
  have : ((29 * max N 10 : ℕ) : ℝ) ≤ ((2 ^ max N 10 : ℕ) : ℝ) := by exact_mod_cast h29
  have : (c.size : ℝ) ≤ 29 := by exact_mod_cast hs
  push_cast at *
  nlinarith

-- `Cslib.Circuits.Boolean.Lupanov.exists_circuit` idx 1: necessary (ε = -1 forces zero gates; constant true needs one)
theorem w1c0r104 : ¬ drop0% Cslib.Circuits.Boolean.Lupanov.exists_circuit 1 := fun h => by
  obtain ⟨m, hm⟩ := h (-1)
  obtain ⟨c, hc, hs⟩ := hm m le_rfl (fun _ => true)
  have := noZeroTrue m c (fun x _ => hc x)
  have : (1 : ℝ) ≤ c.size := by exact_mod_cast this
  norm_num at hs
  linarith

-- `Cslib.Circuits.Boolean.Lupanov.complexity_le` idx 1: necessary (ε = -1; constant true has complexity ≥ 1)
theorem w1c0r105 : ¬ drop0% Cslib.Circuits.Boolean.Lupanov.complexity_le 1 := fun h => by
  obtain ⟨m, hm⟩ := h (-1)
  have hs := hm m le_rfl (fun _ => true)
  have h1 : 1 ≤ Cslib.Circuits.complexity Cslib.Circuits.Boolean.interpretation
      (Cslib.Circuits.single fun (_ : Fin m → Bool) => true) :=
    Cslib.Circuits.le_complexityOn_iff.mpr fun c hc => noZeroTrue m c hc
  have : (1 : ℝ) ≤ (Cslib.Circuits.complexity Cslib.Circuits.Boolean.interpretation
      (Cslib.Circuits.single fun (_ : Fin m → Bool) => true) : ℕ) := by exact_mod_cast h1
  norm_num at hs
  linarith

end

section
open W1c0

-- `Cslib.Circuits.Synthesis.exists_mem` idx 6: necessary (one index, f = XOR at cost 0: XOR needs three gates)
theorem w1c0r112 : ¬ drop0% Cslib.Circuits.Synthesis.exists_mem 6 := fun h => by
  obtain ⟨g, p, hg, -, ht⟩ := h (n := 2) (ι := Unit) (s := Cslib.Circuits.inputs 2) {()} (fun _ => xor2)
    (fun _ => 0) 0 .empty (Cslib.Circuits.inputs_subset_available _)
  have he : (fun x => decide (∃ i ∈ ({()} : Finset Unit), xor2 x = true)) = xor2 := by
    funext x; simp
  simp at hg
  exact xor2_no p (by omega) (he ▸ ht rfl)

-- `Cslib.Circuits.Synthesis.forall_mem` idx 6: necessary (one index, f = XOR at cost 0)
theorem w1c0r113 : ¬ drop0% Cslib.Circuits.Synthesis.forall_mem 6 := fun h => by
  obtain ⟨g, p, hg, -, ht⟩ := h (n := 2) (ι := Unit) (s := Cslib.Circuits.inputs 2) {()} (fun _ => xor2)
    (fun _ => 0) 0 .empty (Cslib.Circuits.inputs_subset_available _)
  simp at hg
  have hm := ht (Set.mem_singleton _)
  refine xor2_no p (by omega) ?_
  convert hm using 1
  funext x; simp

end

section
open W1c0 Cslib Filter

-- `Cslib.Query.IsSort.eval_eq` idx 8: necessary (rock-paper-scissors on Fin 3; merge sort vs merge sort of the reverse)
theorem w1c0r20 : ¬ drop0% Cslib.Query.IsSort.eval_eq 8 := fun h => by
  have := @h (Fin 3) _ _ Cslib.Query.mergeSort_isSort revSort rps _ _ _
    (leOr fun a b => decide (rps a b)) (fun _ _ => rfl) [0, 1, 2]
  simp [leOr, rps, List.mergeSort, List.MergeSort.Internal.splitInTwo] at this

-- `Cslib.LTS.pairLang_regular` idx 2: necessary (counter LTS on ℕ: pairLang 0 0 contains trueⁿfalseⁿ only for equal counts)
theorem w1c0r83 : ¬ drop0% Cslib.LTS.pairLang_regular 2 := fun h =>
  notReg _ (fun n => ctr_updown n) (fun _ _ hm => ctr_count hm) (h (lts := ctr) (s := 0) (t := 0))

-- `Cslib.LTS.pairViaLang_regular` idx 2: necessary (counter LTS on ℕ, via {0})
theorem w1c0r84 : ¬ drop0% Cslib.LTS.pairViaLang_regular 2 := fun h =>
  notReg _ (fun n => LTS.mem_pairViaLang.mpr ⟨0, rfl, _, [], ctr_updown n, .refl, by simp⟩)
    (fun _ _ hm => by
      obtain ⟨r, hr, xs1, xs2, h1, h2, he⟩ := LTS.mem_pairViaLang.mp hm
      exact ctr_count (he ▸ LTS.MTr.comp ctr h1 h2))
    (h (lts := ctr) (via := {0}) (s := 0) (t := 0))

-- `Cslib.Automata.NA.Buchi.language_eq_fin_iSup_hmul_omegaPow` idx 3: necessary (successor automaton on ℕ: accepting run but no state repeats)
theorem w1c0r85 : ¬ drop0% Cslib.Automata.NA.Buchi.language_eq_fin_iSup_hmul_omegaPow 3 := fun h => by
  have hmem : (⟨fun _ => ()⟩ : ωSequence Unit) ∈ Automata.ωAcceptor.language nbS :=
    ⟨⟨fun k => k⟩, ⟨rfl, fun k => rfl⟩, Eventually.frequently (Eventually.of_forall fun _ => Set.mem_univ _)⟩
  rw [h] at hmem
  simp only [ωLanguage.mem_iSup, ωLanguage.mem_hmul] at hmem
  obtain ⟨s, hs, t, ht, xl, hxl, xs, hxs, -⟩ := hmem
  obtain ⟨xls, -, hk⟩ := ωLanguage.mem_omegaPow.mp hxs
  obtain ⟨h1, h2⟩ := hk 0
  have := nbS_mtr h1
  have : xls 0 = [] := List.eq_nil_of_length_eq_zero (by omega)
  exact h2 this

end

section
open W1c0 Cslib Cslib.Automata Cslib.Automata.NA Acceptor

-- `Cslib.Automata.NA.FinAcc.loop_language_eq` idx 4: removable (if na accepts nothing, a path of the loop back to the hub is empty, so both sides are {[]})
theorem w1c0r82 : drop% Cslib.Automata.NA.FinAcc.loop_language_eq 4 := by
  intro Symbol State na _inst
  by_cases hl : language na = 0
  · ext xl; constructor
    · rintro ⟨s, hs, t, ht, hm⟩
      simp only [Set.mem_singleton_iff] at hs ht
      subst hs ht
      rcases back na hm rfl with rfl | ⟨xs, hxs⟩
      · exact Language.nil_mem_kstar _
      · rw [hl] at hxs; exact absurd hxs (Language.notMem_zero _)
    · intro hx
      rw [hl] at hx
      obtain ⟨L, rfl, hL⟩ := Language.mem_kstar.mp hx
      rcases L with _ | ⟨y, L⟩
      · exact ⟨.inl (), rfl, .inl (), rfl, .refl⟩
      · exact absurd (hL y (by simp)) (Language.notMem_zero _)
  · exact Cslib.Automata.NA.FinAcc.loop_language_eq hl

end

section
open W1c0

-- `Cslib.Circuits.Boolean.Lupanov.exists_circuit_of_split` idx 5: necessary (s = 0, k = d = m: bound m m 0 ≪ 2^(2m)/(2m), Shannon's hard function)
theorem w1c0r103 : ¬ drop0% _private.Cslib.Computability.Circuit.Boolean.Lupanov.«0».Cslib.Circuits.Boolean.Lupanov.exists_circuit_of_split 5 := fun h => by
  obtain ⟨m, -, f, hf⟩ := hard00
  obtain ⟨c, hc, hs⟩ := h (n := m + m) (k := m) (d := m) (s := 0) rfl f
  exact absurd (hf c hc) (by omega)

-- `Cslib.Circuits.Boolean.Lupanov.synthesis` idx 4: necessary (s = 0, k = d = m: Shannon's hard function)
theorem w1c0r106 : ¬ drop0% Cslib.Circuits.Boolean.Lupanov.synthesis 4 := fun h => by
  obtain ⟨m, -, f, hf⟩ := hard00
  obtain ⟨c, hc, hs⟩ := (h (k := m) (d := m) (s := 0) f).exists_circuit
  exact absurd (hf c hc) (by omega)

end

section
open W1c0

-- `Cslib.Automata.NA.εTransducer.MTransl.comp` idx 15: necessary (no transitions; first part [some ()])
theorem w1c0r62 : ¬ drop0% Cslib.Automata.NA.εTransducer.MTransl.comp 15 := fun h => by
  have := @h (Option Unit) (Option Unit) _ _ Unit _ _ trN () () () [some ()] [] [] [] ⟨[], .refl, rfl, rfl⟩
  simpa using trN_nil this

-- `Cslib.Automata.NA.εTransducer.MTransl.comp` idx 16: necessary (no transitions; second part [some ()])
theorem w1c0r63 : ¬ drop0% Cslib.Automata.NA.εTransducer.MTransl.comp 16 := fun h => by
  have := @h (Option Unit) (Option Unit) _ _ Unit _ _ trN () () () [] [some ()] [] [] ⟨[], .refl, rfl, rfl⟩
  simpa using trN_nil this

end

