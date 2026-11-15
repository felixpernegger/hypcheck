import Lean.Elab.Command
import Iris
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

open Iris Iris.BI

namespace T3c1

inductive Ix | lo | hi deriving DecidableEq, Inhabited
instance leIx : LE Ix := ⟨fun a b => a = .lo ∨ b = .hi⟩
instance : Std.IsPreorder Ix where
  le_refl a := by cases a <;> simp [LE.le]
  le_trans a b c h1 h2 := by cases a <;> cases b <;> cases c <;> simp_all [LE.le]
def I2 : BiIndex := ⟨Ix, leIx⟩

/-- world map: index lo at step 0 is sent to hi, everything else keeps its index -/
def g : Ix → Nat → Ix
  | .lo, 0 => .hi
  | .lo, _ + 1 => .lo
  | .hi, _ => .hi

theorem g_anti {i : Ix} {n m : Nat} (h : m ≤ n) : leIx.le (g i n) (g i m) := by
  cases i <;> cases n <;> cases m <;> simp [g, LE.le] <;> omega

theorem g_mono {i j : Ix} {n : Nat} (h : leIx.le i j) : leIx.le (g i n) (g j n) := by
  cases i <;> cases j <;> cases n <;> simp_all [g, LE.le]

/-- the embedding at an index: read P at index g i n, one step earlier -/
def eA (P : MonPred I2 SiProp) (i : Ix) : SiProp where
  holds n := (P.monPred_at (g i n)).holds (n - 1)
  closed {n₁ n₂} h hle :=
    P.monPred_mono (I := I2) (g_anti (i := i) hle) _ ((P.monPred_at (g i n₁)).closed h (by omega))

def eM (P : MonPred I2 SiProp) : MonPred I2 SiProp where
  monPred_at := eA P
  monPred_mono {i j} h := fun n hp => P.monPred_mono (I := I2) (g_mono (n := n) h) _ hp

theorem g_zero (i : Ix) : g i 0 = .hi := by cases i <;> rfl
theorem g_succ (i : Ix) (n : Nat) : g i (n + 1) = i := by cases i <;> rfl

theorem eM_holds (P : MonPred I2 SiProp) (i : Ix) (n : Nat) :
    ((eM P).monPred_at i).holds n = (P.monPred_at (g i n)).holds (n - 1) := rfl

/-- implication in MonPred I2 SiProp, unfolded -/
theorem impH (P Q : MonPred I2 SiProp) (i : Ix) (n : Nat) :
    ((iprop(P → Q) : MonPred I2 SiProp).monPred_at i).holds n ↔
      ∀ j, leIx.le i j → ∀ m, m ≤ n → (P.monPred_at j).holds m → (Q.monPred_at j).holds m := by
  constructor
  · intro h j hj m hm hp
    exact h _ ⟨j, rfl⟩ m hm hj m (Nat.le_refl m) hp
  · intro h k ⟨j, e⟩
    subst e
    intro n1 hn1 hj n2 hn2 hp
    exact h j hj n2 (by omega) hp

/-- wand in MonPred I2 SiProp, unfolded (same as implication) -/
theorem wandH (P Q : MonPred I2 SiProp) (i : Ix) (n : Nat) :
    ((iprop(P -∗ Q) : MonPred I2 SiProp).monPred_at i).holds n ↔
      ∀ j, leIx.le i j → ∀ m, m ≤ n → (P.monPred_at j).holds m → (Q.monPred_at j).holds m :=
  impH P Q i n

theorem eImp (P Q : MonPred I2 SiProp) (i : Ix) (n : Nat)
    (H : ∀ j, leIx.le i j → ∀ m, m ≤ n → ((eM P).monPred_at j).holds m → ((eM Q).monPred_at j).holds m) :
    ∀ k, leIx.le (g i n) k → ∀ m, m ≤ n - 1 → (P.monPred_at k).holds m → (Q.monPred_at k).holds m := by
  intro k hk m hm hp
  cases n with
  | zero =>
    have e : m = 0 := by omega
    subst e
    rw [g_zero] at hk
    have : k = .hi := by rcases hk with hk | hk <;> simp_all
    subst this
    have := H i (by cases i <;> first | exact Or.inl rfl | exact Or.inr rfl) 0 (Nat.le_refl 0)
    rw [eM_holds, eM_holds, g_zero] at this
    exact this hp
  | succ n' =>
    rw [g_succ] at hk
    have := H k hk (m + 1) (by omega)
    rw [eM_holds, eM_holds, g_succ] at this
    exact this hp

@[instance_reducible] def eE : BiEmbed (MonPred I2 SiProp) (MonPred I2 SiProp) where
  embed := eM
  ne := ⟨fun {n x y} h i m hm => h (g i m) (show m - 1 ≤ n by omega)⟩
  mono := fun h i n hp => h (g i n) (n - 1) hp
  emp_valid_inj := fun P h i n _ =>
    P.monPred_mono (I := I2) (show leIx.le Ix.lo i from Or.inl rfl) n (h .lo (n + 1) trivial)
  emp_2 := fun _ _ _ => trivial
  impl_2 := fun P Q i n h => (impH P Q (g i n) (n - 1)).2 (eImp P Q i n ((impH _ _ i n).1 h))
  forall_2 := fun Ψ R h i n hr p ⟨q, hq, e⟩ => e ▸ h q hq i n hr
  exist_1 := fun Ψ R h i n ⟨p, ⟨q, hq, e⟩, hp⟩ => h q hq i n (by subst e; exact hp)
  sep := fun P Q => ⟨fun _ _ h => h, fun _ _ h => h⟩
  wand_2 := fun P Q i n h => (wandH P Q (g i n) (n - 1)).2 (eImp P Q i n ((wandH _ _ i n).1 h))
  persistently := fun P => ⟨fun _ _ h => h, fun _ _ h => h⟩


/-- Q0: false at lo, true at hi -/
def Q0 : MonPred I2 SiProp where
  monPred_at i := match i with | .lo => iprop(False) | .hi => iprop(True)
  monPred_mono {i j} h := by
    cases i <;> cases j
    · exact fun _ h => h
    · exact fun _ _ => trivial
    · exact absurd h (fun h' => by rcases h' with h' | h' <;> cases h')
    · exact fun _ h => h

theorem bad : ¬ ((iprop(■ eM Q0) : MonPred I2 SiProp) ⊢ eM iprop(■ Q0)) := fun h => by
  have h1 := h .lo 0 (by
    rintro p ⟨i, rfl⟩
    cases i <;> trivial)
  exact h1 _ ⟨.lo, rfl⟩

end T3c1

-- `Iris.ProofMode.fromModal_plainly_embed` idx 5: necessary (P1 = P2 = MonPred over the two-point index lo < hi with SiProp; the embedding is the pullback along the world map (lo,0) to (hi,0), (i,n+1) to (i,n), (hi,0) to (hi,0); it is a lawful BiEmbed but not BiEmbedSbi; with Q0 false at lo and true at hi, P = plainly Q0, phi = True, plainly of the embedding of Q0 holds at (lo,0) while the embedding of plainly Q0 does not)
theorem t3c1_1 : ¬ drop0% Iris.ProofMode.fromModal_plainly_embed 5 := fun h => by
  have := (@h (MonPred T3c1.I2 SiProp) (MonPred T3c1.I2 SiProp) _ _ T3c1.eE Unit True
    .in () iprop(■ T3c1.Q0) T3c1.Q0 ⟨fun _ => .rfl⟩).from_modal trivial
  exact T3c1.bad this
