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
namespace W3c1
open Iris Iris.OFE

/-- Truncation OFE on naturals (copy of Probe1's TN): dist n x y iff min x (n+1) = min y (n+1). -/
structure TN where v : Nat
instance tnOFE : OFE TN where
  Dist n x y := min x.v (n+1) = min y.v (n+1)
  dist_eqv := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩
  eq_dist' {x y} := ⟨fun h n => h ▸ rfl, fun h => by
      cases x with | mk a => cases y with | mk b =>
      have h' : min a (a+b+1) = min b (a+b+1) := h (a+b)
      simp only [TN.mk.injEq]; omega⟩
  dist_lt {n x y m} h hm := by
    have h' : min x.v (n+1) = min y.v (n+1) := h
    show min x.v (m+1) = min y.v (m+1); omega
theorem tn_dist {n} {x y : TN} : x ≡{n}≡ y ↔ min x.v (n+1) = min y.v (n+1) := Iff.rfl
theorem tn12 : (⟨1⟩ : TN) ≡{0}≡ ⟨2⟩ := rfl
theorem tn12ne : (⟨1⟩ : TN) ≠ ⟨2⟩ := by simp
theorem tn12_1 : ¬ (⟨1⟩ : TN) ≡{1}≡ ⟨2⟩ := by simp [tn_dist]
theorem tn01 : ¬ (⟨0⟩ : TN) ≡{0}≡ ⟨1⟩ := by simp [tn_dist]
instance tn0disc : DiscreteE (⟨0⟩ : TN) := ⟨fun {y} h => by
  cases y with | mk v =>
    have h' : min 0 (0+1) = min v (0+1) := h
    have : v = 0 := by omega
    subst this; rfl⟩
theorem tn1_not_disc : ¬ DiscreteE (⟨1⟩ : TN) := fun h => tn12ne (h.discrete tn12)
/-- Not non-expansive: 1 ↦ 0, else ↦ 1 (1 and 2 agree at 0, images do not). -/
def bad (x : TN) : TN := if x.v = 1 then ⟨0⟩ else ⟨1⟩
theorem bad_not_ne : ¬ bad ⟨1⟩ ≡{0}≡ bad ⟨2⟩ := by simp [bad, tn_dist]
/-- Successor on TN is contractive. -/
def tsucc (x : TN) : TN := ⟨x.v + 1⟩
instance tsuccC : Contractive tsucc := ⟨fun {n x y} h => by
  cases n with
  | zero => show min (x.v+1) 1 = min (y.v+1) 1; omega
  | succ n =>
    have h' : min x.v (n+1) = min y.v (n+1) := h n (Nat.lt_succ_self n)
    show min (x.v+1) (n+2) = min (y.v+1) (n+2); omega⟩

/-- Discrete COFE on Bool. -/
structure DB where v : Bool
deriving DecidableEq
instance dbCOFE : COFE DB := COFE.ofDiscrete DB
instance dbDisc : OFE.Discrete DB := ⟨id⟩
instance : Inhabited DB := ⟨⟨false⟩⟩

/-- Cantor space: Bool streams, n-equal iff they agree on indices ≤ n. A non-discrete COFE. -/
structure CS where s : Nat → Bool
instance csOFE : OFE CS where
  Dist n x y := ∀ k, k ≤ n → x.s k = y.s k
  dist_eqv := ⟨fun _ _ _ => rfl, fun h k hk => (h k hk).symm, fun h1 h2 k hk => (h1 k hk).trans (h2 k hk)⟩
  eq_dist' {x y} := ⟨fun h n k _ => h ▸ rfl, fun h => by
      cases x with | mk a => cases y with | mk b =>
      congr; funext k; exact h k k (Nat.le_refl k)⟩
  dist_lt {n x y m} h hm k hk := h k (by omega)
theorem cs_dist {n} {x y : CS} : x ≡{n}≡ y ↔ ∀ k, k ≤ n → x.s k = y.s k := Iff.rfl
instance csCOFE : IsCOFE CS where
  compl c := ⟨fun k => (c.chain k).s k⟩
  conv_compl {n c} k hk := ((c.cauchy hk) k (Nat.le_refl k)).symm
instance : Inhabited CS := ⟨⟨fun _ => false⟩⟩
theorem cs_compl (c : Chain CS) : (IsCOFE.compl c).s = fun k => (c.chain k).s k := rfl
/-- All-false and all-true streams; `cT 0` vs `cF` differ at index 0. -/
def cF : CS := ⟨fun _ => false⟩
def cT : CS := ⟨fun _ => true⟩
theorem cTF0 : ¬ cT ≡{0}≡ cF := fun h => nomatch h 0 (Nat.le_refl 0)
theorem cTF : cT ≠ cF := fun h => cTF0 (h ▸ Dist.rfl)
/-- Shift right inserting false: contractive. -/
def shift (x : CS) : CS := ⟨fun k => match k with | 0 => false | k+1 => x.s k⟩
instance shiftC : Contractive shift := ⟨fun {n x y} h k hk => by
  cases k with
  | zero => rfl
  | succ k => exact h k (by omega) k (Nat.le_refl k)⟩
theorem shift_cF : cF = shift cF := by
  show (⟨fun _ => false⟩ : CS) = ⟨fun k => match k with | 0 => false | k+1 => false⟩
  congr; funext k; cases k <;> rfl
/-- Chain whose elements each contain a `true` (at index n+1) but whose limit is all false. -/
def escC : Chain CS where
  chain i := ⟨fun k => decide (k = i + 1)⟩
  cauchy {n i} h k hk := by
    show decide (k = i + 1) = decide (k = n + 1)
    have h1 : k ≠ i + 1 := by omega
    have h2 : k ≠ n + 1 := by omega
    simp [h1, h2]
theorem escC_compl : IsCOFE.compl escC = cF := by
  show (⟨fun k => decide (k = k + 1)⟩ : CS) = ⟨fun _ => false⟩
  congr; funext k; simp
/-- "Has some true": not limit preserving. -/
def hasT (x : CS) : Prop := ∃ k, x.s k = true
theorem hasT_esc (n : Nat) : hasT (escC.chain n) := ⟨n+1, by simp [escC]⟩
theorem not_hasT_cF : ¬ hasT cF := fun ⟨_, h⟩ => nomatch h
theorem hasT_not_lp : ¬ LimitPreserving hasT := fun h =>
  not_hasT_cF (escC_compl ▸ h.compl escC hasT_esc)

/-- Setoid on Bool relating everything, and the equality setoid. -/
def bTriv : Setoid Bool := ⟨fun _ _ => True, ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩⟩
def bEq : Setoid Bool := ⟨Eq, ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩⟩
/-- Step-indexed relation on Bool not symmetric at step 0 (false ~ true only). -/
def dq (n : Nat) (a b : Bool) : Prop := a = b ∨ (n = 0 ∧ a = false)
/-- Step-indexed equivalences on Bool that are not downward closed (everything related at step 1). -/
def dr (n : Nat) (a b : Bool) : Prop := a = b ∨ n = 1
/-- Projection-like non-expansive maps for curried rows. -/
def badp (p : TN × TN) : TN := bad p.1
def bad3 (p : TN × TN × TN) : TN := bad p.1
def bad4 (p : TN × TN × TN × TN) : TN := bad p.1

/-- Zero out index 0: non-expansive, 0-close to `shift`, not contractive. -/
def z0 (x : CS) : CS := ⟨fun k => if k = 0 then false else x.s k⟩
instance z0NE : NonExpansive z0 := ⟨fun {n x y} h k hk => by
  show (if k = 0 then false else x.s k) = (if k = 0 then false else y.s k)
  split
  · rfl
  · exact h k hk⟩
/-- Stream true only at index 1. -/
def e1 : CS := ⟨fun k => decide (k = 1)⟩
theorem z0_shift (z : CS) : z0 z ≡{0}≡ shift z := fun k hk => by
  have : k = 0 := by omega
  subst this; rfl
theorem z0_not_contr : ¬ Contractive z0 := fun h => by
  have := h.distLater_dist (n := 1) (x := cF) (y := e1) (distLater_succ.mpr (fun k hk => by
    have : k = 0 := by omega
    subst this; rfl)) 1 (Nat.le_refl 1)
  simp [z0, cF, e1] at this
theorem id_not_contr : ¬ Contractive (fun x : CS => x) := fun h =>
  cTF0 (h.distLater_dist (n := 0) (x := cT) (y := cF) distLater_zero)
/-- Two maps whose second iterates are constant (fixpoints differ at index 0) and which are 0-close pointwise. -/
def kf (w : CS) : CS := ⟨fun k => if k = 0 then w.s 1 else if k = 1 then true else false⟩
def kg (w : CS) : CS := ⟨fun k => if k = 0 then w.s 1 else false⟩
instance kfC : Contractive (Nat.repeat kf 2) := ⟨fun _ _ _ => rfl⟩
instance kgC : Contractive (Nat.repeat kg 2) := ⟨fun _ _ _ => rfl⟩
/-- Maps on TN that are 0-close pointwise, but whose second iterates at 3 are not. -/
def rg (x : TN) : TN := ⟨if x.v = 1 then 0 else if x.v = 2 then 1 else if x.v = 3 then 2 else x.v⟩
def rf (x : TN) : TN := ⟨if x.v = 3 then 1 else (rg x).v⟩
theorem rf_rg (z : TN) : rf z ≡{0}≡ rg z := by
  rcases z with ⟨v⟩
  show min _ 1 = min _ 1
  simp only [rf, rg]
  by_cases h1 : v = 1 <;> by_cases h2 : v = 2 <;> by_cases h3 : v = 3 <;> simp [h1, h2, h3] <;> omega
/-- Constant contractive maps on DB, and their fixpoints. -/
def cst (b : Bool) : DB -c> DB := (fun _ : DB => (⟨b⟩ : DB)).toContractiveHom
theorem fix_cst (b : Bool) : fixpoint (cst b).f = ⟨b⟩ := (fixpoint_unique (f := cst b) rfl).symm
theorem fixc (b : Bool) : fixpoint (fun _ : DB => (⟨b⟩ : DB)) = ⟨b⟩ :=
  (fixpoint_unique (f := (fun _ : DB => (⟨b⟩ : DB)).toContractiveHom) rfl).symm
instance rc1 (b : Bool) : Contractive (Nat.repeat (fun _ : DB => (⟨b⟩ : DB)) 1) := ⟨fun _ => rfl⟩
theorem fixK1 (b : Bool) : fixpointK 1 (fun _ : DB => (⟨b⟩ : DB)) = ⟨b⟩ := fixpointK_unfold 1 _
instance rs1 : Contractive (Nat.repeat shift 1) := ⟨fun h => shiftC.distLater_dist h⟩
theorem db_lp (P : DB → Prop) : LimitPreserving P :=
  LimitPreserving.discrete (fun h hp => (Discrete.discrete_0 h) ▸ hp)
/-- Two-argument contractive data for the fixpointA/B rows. -/
def fAc (b : Bool) : DB -c> DB -n> DB := (fun _ : DB => (Hom.const ⟨b⟩ : DB -n> DB)).toContractiveHom
def fAid : DB -c> DB -n> DB := (fun _ : DB => (Hom.id : DB -n> DB)).toContractiveHom
def fBc (b : Bool) : DB -c> DB -c> DB := (fun _ : DB => cst b).toContractiveHom
def gAc (c : CS) : CS -c> CS -n> CS := (fun _ : CS => (Hom.const c : CS -n> CS)).toContractiveHom
def shC (x : CS) : CS -c> CS := (fun _ : CS => shift x).toContractiveHom
instance shCC : Contractive shC := ⟨fun h _ => shiftC.distLater_dist h⟩
def gBs : CS -c> CS -c> CS := shC.toContractiveHom

end W3c1
open W3c1 Iris Iris.OFE

-- `Iris.OFE.dist_lt` (hypothesis 7): necessary, TN: 1 and 2 agree at 0, not at 1
theorem w3c1_1 : ¬ drop0% Iris.OFE.dist_lt 7 := fun h => tn12_1 (@h TN _ 0 ⟨1⟩ ⟨2⟩ 1 tn12)
-- `Iris.OFE.NonExpansive.comp` (hypothesis 8): necessary, g = bad, f = id on TN
theorem w3c1_2 : ¬ drop0% Iris.OFE.NonExpansive.comp 8 := fun h =>
  bad_not_ne ((@h TN TN TN _ _ _ bad id id_ne).ne tn12)
-- `Iris.OFE.NonExpansive.comp` (hypothesis 9): necessary, g = id, f = bad on TN
theorem w3c1_3 : ¬ drop0% Iris.OFE.NonExpansive.comp 9 := fun h =>
  bad_not_ne ((@h TN TN TN _ _ _ id bad id_ne).ne tn12)
-- `Iris.OFE.NonExpansive₂.ne` (hypothesis 11): necessary, f x y = x on TN, x 0 vs 1
theorem w3c1_4 : ¬ drop0% Iris.OFE.NonExpansive₂.ne 11 := fun h =>
  tn01 (@h TN TN TN _ _ _ (fun x _ => x) ⟨fun _ _ _ hx _ _ _ => hx⟩ 0 ⟨0⟩ ⟨1⟩ ⟨0⟩ ⟨0⟩ Dist.rfl)
-- `Iris.OFE.NonExpansive₂.ne` (hypothesis 14): necessary, f x y = y on TN, y 0 vs 1
theorem w3c1_5 : ¬ drop0% Iris.OFE.NonExpansive₂.ne 14 := fun h =>
  tn01 (@h TN TN TN _ _ _ (fun _ y => y) ⟨fun _ _ _ _ _ _ hy => hy⟩ 0 ⟨0⟩ ⟨0⟩ Dist.rfl ⟨0⟩ ⟨1⟩)
-- `Iris.OFE.NonExpansive₂.ne_right` (hypothesis 7): necessary, f x y = bad y
theorem w3c1_6 : ¬ drop0% Iris.OFE.NonExpansive₂.ne_right 7 := fun h =>
  bad_not_ne ((@h TN TN TN _ _ _ (fun _ y => bad y) ⟨0⟩).ne tn12)
-- `Iris.OFE.NonExpansive₂.ne_left` (hypothesis 7): necessary, f x y = bad x
theorem w3c1_7 : ¬ drop0% Iris.OFE.NonExpansive₂.ne_left 7 := fun h =>
  bad_not_ne ((@h TN TN TN _ _ _ (fun x _ => bad x) ⟨0⟩).ne tn12)
-- `Iris.OFE.NonExpansive₃.ne` (hypothesis 9): necessary, f x y z = bad x, x 1 vs 2
theorem w3c1_8 : ¬ drop0% Iris.OFE.NonExpansive₃.ne 9 := fun h =>
  bad_not_ne (@h TN TN TN TN _ _ _ _ (fun x _ _ => bad x) 0 ⟨1⟩ ⟨2⟩ tn12 ⟨0⟩ ⟨0⟩ Dist.rfl ⟨0⟩ ⟨0⟩ Dist.rfl)
-- `Iris.OFE.NonExpansive₃.ne` (hypothesis 13): necessary, f x y z = x, x 0 vs 1
theorem w3c1_9 : ¬ drop0% Iris.OFE.NonExpansive₃.ne 13 := fun h =>
  tn01 (@h TN TN TN TN _ _ _ _ (fun x _ _ => x) ⟨fun _ _ _ hx _ _ _ _ _ _ => hx⟩ 0 ⟨0⟩ ⟨1⟩ ⟨0⟩ ⟨0⟩ Dist.rfl ⟨0⟩ ⟨0⟩ Dist.rfl)
-- `Iris.OFE.NonExpansive₃.ne` (hypothesis 16): necessary, f x y z = y, y 0 vs 1
theorem w3c1_10 : ¬ drop0% Iris.OFE.NonExpansive₃.ne 16 := fun h =>
  tn01 (@h TN TN TN TN _ _ _ _ (fun _ y _ => y) ⟨fun _ _ _ _ _ _ hy _ _ _ => hy⟩ 0 ⟨0⟩ ⟨0⟩ Dist.rfl ⟨0⟩ ⟨1⟩ ⟨0⟩ ⟨0⟩ Dist.rfl)
-- `Iris.OFE.NonExpansive₄.ne` (hypothesis 11): necessary, f x y z w = bad x, x 1 vs 2
theorem w3c1_11 : ¬ drop0% Iris.OFE.NonExpansive₄.ne 11 := fun h =>
  bad_not_ne (@h TN TN TN TN TN _ _ _ _ _ (fun x _ _ _ => bad x) 0 ⟨1⟩ ⟨2⟩ tn12 ⟨0⟩ ⟨0⟩ Dist.rfl ⟨0⟩ ⟨0⟩ Dist.rfl ⟨0⟩ ⟨0⟩ Dist.rfl)
-- `Iris.OFE.NonExpansive₄.ne` (hypothesis 15): necessary, f x y z w = x, x 0 vs 1
theorem w3c1_12 : ¬ drop0% Iris.OFE.NonExpansive₄.ne 15 := fun h =>
  tn01 (@h TN TN TN TN TN _ _ _ _ _ (fun x _ _ _ => x) ⟨fun _ _ _ hx _ _ _ _ _ _ _ _ _ => hx⟩ 0 ⟨0⟩ ⟨1⟩ ⟨0⟩ ⟨0⟩ Dist.rfl ⟨0⟩ ⟨0⟩ Dist.rfl ⟨0⟩ ⟨0⟩ Dist.rfl)
-- `Iris.OFE.NonExpansive₄.ne` (hypothesis 18): necessary, f x y z w = y, y 0 vs 1
theorem w3c1_13 : ¬ drop0% Iris.OFE.NonExpansive₄.ne 18 := fun h =>
  tn01 (@h TN TN TN TN TN _ _ _ _ _ (fun _ y _ _ => y) ⟨fun _ _ _ _ _ _ hy _ _ _ _ _ _ => hy⟩ 0 ⟨0⟩ ⟨0⟩ Dist.rfl ⟨0⟩ ⟨1⟩ ⟨0⟩ ⟨0⟩ Dist.rfl ⟨0⟩ ⟨0⟩ Dist.rfl)
-- `Iris.OFE.NonExpansive₄.ne` (hypothesis 21): necessary, f x y z w = z, z 0 vs 1
theorem w3c1_14 : ¬ drop0% Iris.OFE.NonExpansive₄.ne 21 := fun h =>
  tn01 (@h TN TN TN TN TN _ _ _ _ _ (fun _ _ z _ => z) ⟨fun _ _ _ _ _ _ _ _ _ hz _ _ _ => hz⟩ 0 ⟨0⟩ ⟨0⟩ Dist.rfl ⟨0⟩ ⟨0⟩ Dist.rfl ⟨0⟩ ⟨1⟩ ⟨0⟩ ⟨0⟩ Dist.rfl)
-- `Iris.OFE.NonExpansive₄.ne` (hypothesis 24): necessary, f x y z w = w, w 0 vs 1
theorem w3c1_15 : ¬ drop0% Iris.OFE.NonExpansive₄.ne 24 := fun h =>
  tn01 (@h TN TN TN TN TN _ _ _ _ _ (fun _ _ _ w => w) ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ hw => hw⟩ 0 ⟨0⟩ ⟨0⟩ Dist.rfl ⟨0⟩ ⟨0⟩ Dist.rfl ⟨0⟩ ⟨0⟩ Dist.rfl ⟨0⟩ ⟨1⟩)
-- `Iris.OFE.DistLater.symm` (hypothesis 5): necessary, TN n = 1, 0 vs 1
theorem w3c1_16 : ¬ drop0% Iris.OFE.DistLater.symm 5 := fun h =>
  tn01 (@h TN ⟨0⟩ _ 1 ⟨1⟩ 0 (by omega))
-- `Iris.OFE.DistLater.trans` (hypothesis 6): necessary, TN n = 1, x = 1, y = z = 0
theorem w3c1_17 : ¬ drop0% Iris.OFE.DistLater.trans 6 := fun h =>
  tn01 (@h TN ⟨0⟩ ⟨0⟩ _ 1 ⟨1⟩ DistLater.rfl 0 (by omega)).symm
-- `Iris.OFE.DistLater.trans` (hypothesis 7): necessary, TN n = 1, x = y = 0, z = 1
theorem w3c1_18 : ¬ drop0% Iris.OFE.DistLater.trans 7 := fun h =>
  tn01 (@h TN ⟨0⟩ ⟨1⟩ _ 1 ⟨0⟩ DistLater.rfl 0 (by omega))
-- `Iris.OFE.Dist.distLater` (hypothesis 5): necessary, TN n = 1, 0 vs 1
theorem w3c1_19 : ¬ drop0% Iris.OFE.Dist.distLater 5 := fun h =>
  tn01 (@h TN _ 1 ⟨0⟩ ⟨1⟩ 0 (by omega))
-- `Iris.OFE.Contractive.distLater_dist` (hypothesis 5): necessary, f = id on TN, n = 0
theorem w3c1_20 : ¬ drop0% Iris.OFE.Contractive.distLater_dist 5 := fun h =>
  tn01 (@h TN TN _ _ id 0 ⟨0⟩ ⟨1⟩ distLater_zero)
-- `Iris.OFE.Contractive.distLater_dist` (hypothesis 9): necessary, f = successor on TN (contractive), n = 1, 0 vs 1
theorem w3c1_21 : ¬ drop0% Iris.OFE.Contractive.distLater_dist 9 := fun h =>
  tn12_1 (@h TN TN _ _ tsucc tsuccC 1 ⟨0⟩ ⟨1⟩)
-- `Iris.OFE.Contractive.zero` (hypothesis 5): necessary, f = id on TN
theorem w3c1_22 : ¬ drop0% Iris.OFE.Contractive.zero 5 := fun h =>
  tn01 (@h TN TN _ _ id ⟨0⟩ ⟨1⟩)
-- `Iris.OFE.Contractive.succ` (hypothesis 5): necessary, f = id on TN, n = 0, 1 vs 2
theorem w3c1_23 : ¬ drop0% Iris.OFE.Contractive.succ 5 := fun h =>
  tn12_1 (@h TN TN _ _ id 0 ⟨1⟩ ⟨2⟩ tn12)
-- `Iris.OFE.Contractive.succ` (hypothesis 9): necessary, f = successor on TN, n = 0, 0 vs 1
theorem w3c1_24 : ¬ drop0% Iris.OFE.Contractive.succ 9 := fun h =>
  tn12_1 (@h TN TN _ _ tsucc tsuccC 0 ⟨0⟩ ⟨1⟩)
-- `Iris.OFE.ne_of_contractive` (hypothesis 5): necessary, f = bad
theorem w3c1_25 : ¬ drop0% Iris.OFE.ne_of_contractive 5 := fun h =>
  bad_not_ne ((@h TN TN _ _ bad).ne tn12)
-- `Iris.OFE.Contractive.dist_later_dist` (hypothesis 5): necessary, f = id on TN, n = 0
theorem w3c1_26 : ¬ drop0% Iris.OFE.Contractive.dist_later_dist 5 := fun h =>
  tn01 (@h TN TN _ _ id 0 ⟨0⟩ ⟨1⟩ distLater_zero)
-- `Iris.OFE.Contractive.dist_later_dist` (hypothesis 9): necessary, f = successor on TN, n = 1, 0 vs 1
theorem w3c1_27 : ¬ drop0% Iris.OFE.Contractive.dist_later_dist 9 := fun h =>
  tn12_1 (@h TN TN _ _ tsucc tsuccC 1 ⟨0⟩ ⟨1⟩)
-- `Iris.OFE.ne_dist_later` (hypothesis 5): necessary, f = bad, n = 1, 1 vs 2
theorem w3c1_28 : ¬ drop0% Iris.OFE.ne_dist_later 5 := fun h =>
  bad_not_ne (@h TN TN _ _ bad 1 ⟨1⟩ ⟨2⟩ (distLater_succ.mpr tn12) 0 (by omega))
-- `Iris.OFE.ne_dist_later` (hypothesis 9): necessary, f = id, n = 1, 0 vs 1
theorem w3c1_29 : ¬ drop0% Iris.OFE.ne_dist_later 9 := fun h =>
  tn01 (@h TN TN _ _ id id_ne 1 ⟨0⟩ ⟨1⟩ 0 (by omega))
-- `Iris.OFE.discreteE_eq` (hypothesis 4): necessary, TN: 0 discrete, 1 not
theorem w3c1_30 : ¬ drop0% Iris.OFE.discreteE_eq 4 := fun h =>
  tn1_not_disc ((@h TN _ ⟨0⟩ ⟨1⟩).mp tn0disc)
-- `Iris.OFE.ne_of_discrete` (hypothesis 3): necessary, TN not discrete, f = bad
theorem w3c1_31 : ¬ drop0% Iris.OFE.ne_of_discrete 3 := fun h =>
  bad_not_ne ((@h TN TN _ _ bad).ne tn12)
-- `Iris.OFE.Discrete.toDiscreteE` (hypothesis 2): necessary, TN, x = 1
theorem w3c1_32 : ¬ drop0% Iris.OFE.Discrete.toDiscreteE 2 := fun h =>
  tn1_not_disc (@h TN _ ⟨1⟩)
-- `Iris.OFE.Discrete.discrete_iff` (hypothesis 2): necessary, TN, n = 0, 1 vs 2
theorem w3c1_33 : ¬ drop0% Iris.OFE.Discrete.discrete_iff 2 := fun h =>
  tn12ne ((@h TN _ 0 ⟨1⟩ ⟨2⟩).mpr tn12)
-- `Iris.OFE.Discrete.discrete_iff_0` (hypothesis 2): necessary, TN, n = 1, 1 vs 2
theorem w3c1_34 : ¬ drop0% Iris.OFE.Discrete.discrete_iff_0 2 := fun h =>
  tn12_1 ((@h TN _ 1 ⟨1⟩ ⟨2⟩).mp tn12)
-- `Iris.OFE.ofQuotient.lift_mk` (hypothesis 4): necessary (at beta : Type), Bool with the all-relating setoid, f = id
theorem w3c1_35 : ¬ ∀ {X : Type} {s : Setoid X} {β : Type} (f : X → β) (x : X),
    ∀ (x y : X), Setoid.r x y → f x = f y := fun h =>
  nomatch (@h Bool bTriv Bool id true true false trivial)
-- `Iris.OFE.ofQuotient.lift₂_mk` (hypothesis 4): necessary (at beta : Type), Bool with the all-relating setoid, f a b = a
theorem w3c1_36 : ¬ ∀ {X : Type} {s : Setoid X} {β : Type} (f : X → X → β) (x y : X),
    ∀ (a b c d : X), Setoid.r a c → Setoid.r b d → f a b = f c d := fun h =>
  nomatch (@h Bool bTriv Bool (fun a _ => a) true true true true false true trivial trivial)
-- `Iris.OFE.ofQuotient.map_mk` (hypothesis 5): necessary, f = id from the all-relating setoid on Bool to the equality setoid
theorem w3c1_37 : ¬ indep0% Iris.OFE.ofQuotient.map_mk 5 := fun h =>
  nomatch (@h Bool bTriv Bool bEq id true true false trivial : true = false)
-- `Iris.OFE.ofQuotient.dist_mk` (hypothesis 3): necessary, dq on Bool (false ~0 true only) is downward closed with limit Eq but not symmetric
theorem w3c1_38 : ¬ indep0% Iris.OFE.ofQuotient.dist_mk 3 := fun h => by
  have e := @h Bool bEq dq
    (fun {n m x y} hd hm => by
      rcases hd with hd | ⟨hn, _⟩
      · exact Or.inl hd
      · omega)
    (fun x y => ⟨fun hxy n => Or.inl hxy, fun hn => by
      rcases hn 1 with hd | ⟨hd, _⟩
      · exact hd
      · omega⟩) 0 true true 0
  have := e.symm (x := false) (y := true) (Or.inr ⟨rfl, rfl⟩)
  simp [dq] at this
-- `Iris.OFE.ofQuotient.dist_mk` (hypothesis 4): necessary, dr on Bool (everything related at step 1 only): equivalences with limit Eq, not downward closed
theorem w3c1_39 : ¬ indep0% Iris.OFE.ofQuotient.dist_mk 4 := fun h => by
  have e := @h Bool bEq dr
    (fun {n} => ⟨fun _ => Or.inl rfl,
      fun hd => by rcases hd with hd | hd; exact Or.inl hd.symm; exact Or.inr hd,
      fun h1 h2 => by
        rcases h1 with h1 | h1
        · subst h1; exact h2
        · exact Or.inr h1⟩)
    (fun x y => ⟨fun hxy n => Or.inl hxy, fun hn => by
      rcases hn 0 with hd | hd
      · exact hd
      · omega⟩) 0 true true 1 0 true false (Or.inr rfl) (by omega)
  simp [dr] at e
-- `Iris.OFE.ofQuotient.dist_mk` (hypothesis 5): necessary, dist always true but the setoid is equality on Bool
theorem w3c1_40 : ¬ indep0% Iris.OFE.ofQuotient.dist_mk 5 := fun h => by
  have e := @h Bool bEq (fun _ _ _ => True)
    (fun {n} => ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩)
    (fun _ _ => trivial) 0 true true true false
  exact nomatch (e.mpr (fun _ => trivial) : true = false)
-- `Iris.OFE.Hom.ext` (hypothesis 6): necessary, id and the constant 0 on TN differ
theorem w3c1_41 : ¬ drop0% Iris.OFE.Hom.ext 6 := fun h => by
  have := congrArg (fun g : TN -n> TN => (g.f ⟨1⟩).v) (@h TN TN _ _ Hom.id (Hom.const ⟨0⟩))
  simp at this
-- `Iris.OFE.ContractiveHom.ext` (hypothesis 6): necessary, constants 0 and 1 on TN differ
theorem w3c1_42 : ¬ drop0% Iris.OFE.ContractiveHom.ext 6 := fun h => by
  have := congrArg (fun g : TN -c> TN => (g.f ⟨1⟩).v)
    (@h TN TN _ _ (fun _ : TN => (⟨0⟩ : TN)).toContractiveHom (fun _ : TN => (⟨1⟩ : TN)).toContractiveHom)
  simp [Function.toContractiveHom] at this
-- `Function.toContractiveHom_apply` (hypothesis 5): necessary, id on TN is not contractive
theorem w3c1_43 : ¬ indep0% Function.toContractiveHom_apply 5 := fun h =>
  tn01 ((@h TN TN id _ _ ⟨0⟩).distLater_dist (n := 0) (x := ⟨0⟩) (y := ⟨1⟩) distLater_zero)
-- `Iris.OFE.Option.ne_match` (hypothesis 5): necessary, f = bad
theorem w3c1_44 : ¬ drop0% Iris.OFE.Option.ne_match 5 := fun h =>
  bad_not_ne ((@h TN _ TN _ bad ⟨0⟩).ne (x₁ := some ⟨1⟩) (x₂ := some ⟨2⟩) tn12)
-- `Iris.OFE.Option.bind_fun_ne` (hypothesis 5): necessary, f 1 = some 0, else none
theorem w3c1_45 : ¬ drop0% Iris.OFE.Option.bind_fun_ne 5 := fun h => by
  have := (@h TN TN _ _ (fun x => if x.v = 1 then some ⟨0⟩ else none)).ne (x₁ := some ⟨1⟩) (x₂ := some ⟨2⟩) tn12
  simp [flip] at this
-- `Iris.OFE.ofe_mor_car_proper` (hypothesis 6): necessary, id and constant 0 on TN at 1
theorem w3c1_46 : ¬ drop0% Iris.OFE.ofe_mor_car_proper 6 := fun h => by
  have := congrArg TN.v (@h TN TN _ _ Hom.id (Hom.const ⟨0⟩) ⟨1⟩ ⟨1⟩ rfl)
  simp at this
-- `Iris.OFE.mapCod_lookup_discrete` (hypothesis 5): necessary, beta () = TN, f () = 1
theorem w3c1_47 : ¬ drop0% Iris.OFE.mapCod_lookup_discrete 5 := fun h =>
  tn1_not_disc (@h Unit (fun _ => TN) (fun _ => tnOFE) (fun _ => ⟨1⟩) ())
-- `Iris.OFE.NonExpansive₂.uncurry` (hypothesis 7): necessary, f x y = bad x
theorem w3c1_48 : ¬ drop0% Iris.OFE.NonExpansive₂.uncurry 7 := fun h =>
  bad_not_ne ((@h TN TN TN _ _ _ (fun x _ => bad x)).ne (x₁ := (⟨1⟩, ⟨0⟩)) (x₂ := (⟨2⟩, ⟨0⟩)) ⟨tn12, Dist.rfl⟩)
-- `Iris.OFE.NonExpansive.curry` (hypothesis 7): necessary, f p = bad p.1
theorem w3c1_49 : ¬ drop0% Iris.OFE.NonExpansive.curry 7 := fun h =>
  bad_not_ne ((@h TN TN TN _ _ _ badp).ne tn12 (Dist.rfl (x := (⟨0⟩ : TN))))
-- `Iris.OFE.NonExpansive.curry₃` (hypothesis 9): necessary, f p = bad p.1
theorem w3c1_50 : ¬ drop0% Iris.OFE.NonExpansive.curry₃ 9 := fun h =>
  bad_not_ne ((@h TN TN TN TN _ _ _ _ bad3).ne tn12 (Dist.rfl (x := (⟨0⟩ : TN))) (Dist.rfl (x := (⟨0⟩ : TN))))
-- `Iris.OFE.NonExpansive₃.uncurry` (hypothesis 9): necessary, f x y z = bad x
theorem w3c1_51 : ¬ drop0% Iris.OFE.NonExpansive₃.uncurry 9 := fun h =>
  bad_not_ne ((@h TN TN TN TN _ _ _ _ (fun x _ _ => bad x)).ne (x₁ := (⟨1⟩, ⟨0⟩, ⟨0⟩)) (x₂ := (⟨2⟩, ⟨0⟩, ⟨0⟩))
    ⟨tn12, Dist.rfl, Dist.rfl⟩)
-- `Iris.OFE.NonExpansive.curry₄` (hypothesis 11): necessary, f p = bad p.1
theorem w3c1_52 : ¬ drop0% Iris.OFE.NonExpansive.curry₄ 11 := fun h =>
  bad_not_ne ((@h TN TN TN TN TN _ _ _ _ _ bad4).ne tn12 (Dist.rfl (x := (⟨0⟩ : TN))) (Dist.rfl (x := (⟨0⟩ : TN)))
    (Dist.rfl (x := (⟨0⟩ : TN))))
-- `Iris.OFE.NonExpansive₄.uncurry` (hypothesis 11): necessary, f x y z w = bad x
theorem w3c1_53 : ¬ drop0% Iris.OFE.NonExpansive₄.uncurry 11 := fun h =>
  bad_not_ne ((@h TN TN TN TN TN _ _ _ _ _ (fun x _ _ _ => bad x)).ne (x₁ := (⟨1⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩))
    (x₂ := (⟨2⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩)) ⟨tn12, Dist.rfl, Dist.rfl, Dist.rfl⟩)
-- `Iris.OFE.prod.is_discrete` (hypothesis 6): necessary, (1, 0) in TN × TN
theorem w3c1_54 : ¬ drop0% Iris.OFE.prod.is_discrete 6 := fun h =>
  tn12ne (congrArg Prod.fst ((@h TN TN _ _ ⟨1⟩ ⟨0⟩ tn0disc).discrete (y := (⟨2⟩, ⟨0⟩)) ⟨tn12, Dist.rfl⟩))
-- `Iris.OFE.prod.is_discrete` (hypothesis 7): necessary, (0, 1) in TN × TN
theorem w3c1_55 : ¬ drop0% Iris.OFE.prod.is_discrete 7 := fun h =>
  tn12ne (congrArg Prod.snd ((@h TN TN _ _ ⟨0⟩ ⟨1⟩ tn0disc).discrete (y := (⟨0⟩, ⟨2⟩)) ⟨Dist.rfl, tn12⟩))
-- `Iris.OFE.instDiscreteProd` (hypothesis 4): necessary, TN × Unit
theorem w3c1_56 : ¬ drop0% Iris.OFE.instDiscreteProd 4 := fun h =>
  tn12ne (congrArg Prod.fst ((@h TN Unit _ _ _).discrete_0 (x := (⟨1⟩, ())) (y := (⟨2⟩, ())) ⟨tn12, trivial⟩))
-- `Iris.OFE.instDiscreteProd` (hypothesis 5): necessary, Unit × TN
theorem w3c1_57 : ¬ drop0% Iris.OFE.instDiscreteProd 5 := fun h =>
  tn12ne (congrArg Prod.snd ((@h Unit TN _ _ _).discrete_0 (x := ((), ⟨1⟩)) (y := ((), ⟨2⟩)) ⟨trivial, tn12⟩))
-- `Iris.OFE.dist_ext_left` (hypothesis 7): necessary, TN, 0 vs 1
theorem w3c1_58 : ¬ drop0% Iris.OFE.dist_ext_left 7 := fun h =>
  tn01 (@h TN Unit _ _ 0 ⟨0⟩ ⟨1⟩)
-- `Iris.OFE.dist_ext_right` (hypothesis 7): necessary, TN, 0 vs 1
theorem w3c1_59 : ¬ drop0% Iris.OFE.dist_ext_right 7 := fun h =>
  tn01 (@h Unit TN _ _ 0 ⟨0⟩ ⟨1⟩)
-- `Iris.OFE.instNonExpansiveElim` (hypothesis 8): necessary, f1 = bad, f2 = id
theorem w3c1_60 : ¬ drop0% Iris.OFE.instNonExpansiveElim 8 := fun h =>
  bad_not_ne ((@h TN TN _ _ TN _ bad id id_ne).ne (x₁ := .inl ⟨1⟩) (x₂ := .inl ⟨2⟩) tn12)
-- `Iris.OFE.instNonExpansiveElim` (hypothesis 9): necessary, f1 = id, f2 = bad
theorem w3c1_61 : ¬ drop0% Iris.OFE.instNonExpansiveElim 9 := fun h =>
  bad_not_ne ((@h TN TN _ _ TN _ id bad id_ne).ne (x₁ := .inr ⟨1⟩) (x₂ := .inr ⟨2⟩) tn12)
-- `Iris.OFE.discreteE_inl` (hypothesis 5): necessary, inl 1 in TN ⊕ Unit
theorem w3c1_62 : ¬ drop0% Iris.OFE.discreteE_inl 5 := fun h =>
  tn12ne (Sum.inl.inj ((@h TN Unit _ _ ⟨1⟩).discrete (y := .inl ⟨2⟩) tn12))
-- `Iris.OFE.discreteE_inr` (hypothesis 5): necessary, inr 1 in Unit ⊕ TN
theorem w3c1_63 : ¬ drop0% Iris.OFE.discreteE_inr 5 := fun h =>
  tn12ne (Sum.inr.inj ((@h Unit TN _ _ ⟨1⟩).discrete (y := .inr ⟨2⟩) tn12))
-- `Iris.OFE.instDiscreteSum` (hypothesis 4): necessary, TN ⊕ Unit
theorem w3c1_64 : ¬ drop0% Iris.OFE.instDiscreteSum 4 := fun h =>
  tn12ne (Sum.inl.inj ((@h TN Unit _ _ _).discrete_0 (x := .inl ⟨1⟩) (y := .inl ⟨2⟩) tn12))
-- `Iris.OFE.instDiscreteSum` (hypothesis 5): necessary, Unit ⊕ TN
theorem w3c1_65 : ¬ drop0% Iris.OFE.instDiscreteSum 5 := fun h =>
  tn12ne (Sum.inr.inj ((@h Unit TN _ _ _).discrete_0 (x := .inr ⟨1⟩) (y := .inr ⟨2⟩) tn12))
-- `Iris.OFE.instDiscreteESubtypeOfVal` (hypothesis 4): necessary, subtype True of TN at 1
theorem w3c1_66 : ¬ drop0% Iris.OFE.instDiscreteESubtypeOfVal 4 := fun h =>
  tn12ne (congrArg Subtype.val ((@h TN _ (fun _ => True) ⟨⟨1⟩, trivial⟩).discrete (y := ⟨⟨2⟩, trivial⟩) tn12))
-- `Iris.OFE.instDiscreteSubtype` (hypothesis 2): necessary, subtype True of TN
theorem w3c1_67 : ¬ drop0% Iris.OFE.instDiscreteSubtype 2 := fun h =>
  tn12ne (congrArg Subtype.val ((@h TN _ (fun _ => True)).discrete_0 (x := ⟨⟨1⟩, trivial⟩) (y := ⟨⟨2⟩, trivial⟩) tn12))
-- `Iris.OFE.exist_ne` (hypothesis 6): necessary, TN, P a = (a = 2), a1 = 1, a2 = 2
theorem w3c1_68 : ¬ indep0% Iris.OFE.exist_ne 6 := fun h =>
  tn12ne (@h TN _ (fun a => a = ⟨2⟩) 0 ⟨1⟩ ⟨2⟩ rfl tn12)
-- `Iris.OFE.exist_ne` (hypothesis 8): necessary, TN, P = True, 0 vs 1
theorem w3c1_69 : ¬ drop0% Iris.OFE.exist_ne 8 := fun h =>
  tn01 (@h TN _ (fun _ => True) 0 ⟨0⟩ ⟨1⟩ trivial trivial)
-- `Iris.OFE.instDiscreteESigma` (hypothesis 4): necessary, Sigma over Unit of TN at 1
theorem w3c1_70 : ¬ drop0% Iris.OFE.instDiscreteESigma 4 := fun h => by
  have e := (@h Unit (fun _ => TN) (fun _ => tnOFE) ⟨(), ⟨1⟩⟩).discrete (y := ⟨(), ⟨2⟩⟩) ⟨rfl, tn12⟩
  have := congrArg (fun s : (Σ _ : Unit, TN) => s.2.v) e
  simp at this
-- `Iris.OFE.instDiscreteSigma` (hypothesis 3): necessary, Sigma over Unit of TN
theorem w3c1_71 : ¬ drop0% Iris.OFE.instDiscreteSigma 3 := fun h => by
  have e := (@h Unit (fun _ => TN) (fun _ => tnOFE)).discrete_0 (x := ⟨(), ⟨1⟩⟩) (y := ⟨(), ⟨2⟩⟩) ⟨rfl, tn12⟩
  have := congrArg (fun s : (Σ _ : Unit, TN) => s.2.v) e
  simp at this
-- `Iris.OFE.Sigma.dist_proj1` (hypothesis 6): necessary, first components true vs false
theorem w3c1_72 : ¬ drop0% Iris.OFE.Sigma.dist_proj1 6 := fun h =>
  nomatch (@h Bool (fun _ => Unit) (fun _ => unitOFE) 0 ⟨true, ()⟩ ⟨false, ()⟩)
-- `Iris.OFE.Sigma.equiv_proj1` (hypothesis 5): necessary, first components true vs false
theorem w3c1_73 : ¬ drop0% Iris.OFE.Sigma.equiv_proj1 5 := fun h =>
  nomatch (@h Bool (fun _ => Unit) (fun _ => unitOFE) ⟨true, ()⟩ ⟨false, ()⟩)
-- `Iris.OFE.Sigma.dist_fst` (hypothesis 6): necessary, first components true vs false
theorem w3c1_74 : ¬ drop0% Iris.OFE.Sigma.dist_fst 6 := fun h =>
  nomatch (@h Bool (fun _ => Unit) (fun _ => unitOFE) 0 ⟨true, ()⟩ ⟨false, ()⟩)
-- `Iris.OFE.Sigma.dist_snd` (hypothesis 6): necessary, first components true vs false are not close
theorem w3c1_75 : ¬ indep0% Iris.OFE.Sigma.dist_snd 6 := fun h =>
  nomatch (@h Bool (fun _ => Unit) (fun _ => unitOFE) 0 ⟨true, ()⟩ ⟨false, ()⟩).1
-- `Iris.OFE.Sigma.equiv_snd` (hypothesis 5): necessary, first components true vs false
theorem w3c1_76 : ¬ indep0% Iris.OFE.Sigma.equiv_snd 5 := fun h =>
  nomatch congrArg Sigma.fst (@h Bool (fun _ => Unit) (fun _ => unitOFE) ⟨true, ()⟩ ⟨false, ()⟩)
-- `Iris.OFE.Sigma.mk_dist` (hypothesis 8): necessary, indices true vs false
theorem w3c1_77 : ¬ indep0% Iris.OFE.Sigma.mk_dist 8 := fun h =>
  nomatch (@h Bool (fun _ => Unit) (fun _ => unitOFE) 0 true false () ())
-- `Iris.OFE.Sigma.mk_dist` (hypothesis 9): necessary, index (), values 0 vs 1 in TN
theorem w3c1_78 : ¬ drop0% Iris.OFE.Sigma.mk_dist 9 := fun h =>
  tn01 (@h Unit (fun _ => TN) (fun _ => tnOFE) 0 () () ⟨0⟩ ⟨1⟩ rfl).2
-- `Iris.OFE.Sigma.mk_equiv` (hypothesis 7): necessary, indices true vs false
theorem w3c1_79 : ¬ indep0% Iris.OFE.Sigma.mk_equiv 7 := fun h =>
  nomatch (@h Bool (fun _ => Unit) (fun _ => unitOFE) true false () ())
-- `Iris.OFE.Sigma.mk_equiv` (hypothesis 8): necessary, index (), values 0 vs 1 in TN
theorem w3c1_80 : ¬ drop0% Iris.OFE.Sigma.mk_equiv 8 := fun h => by
  have := congrArg (fun s : (Σ _ : Unit, TN) => s.2.v) (@h Unit (fun _ => TN) (fun _ => tnOFE) () () ⟨0⟩ ⟨1⟩ rfl)
  simp at this
-- `Iris.OFE.Iso.ext` (hypothesis 6): removable, the hom of an isomorphism is determined by its inverse
theorem w3c1_81 : drop% Iris.OFE.Iso.ext 6 := by
  intro α β _ _ x y h
  have hh : x.hom = y.hom := by
    apply Hom.ext; funext z
    calc x.hom.f z = x.hom.f (y.inv.f (y.hom.f z)) := by rw [y.inv_hom]
      _ = x.hom.f (x.inv.f (y.hom.f z)) := by rw [h]
      _ = y.hom.f z := x.hom_inv
  exact Iso.ext hh h
-- `Iris.OFE.Iso.ext` (hypothesis 7): removable, the inverse of an isomorphism is determined by its hom
theorem w3c1_82 : drop% Iris.OFE.Iso.ext 7 := by
  intro α β _ _ x y h
  have hi : x.inv = y.inv := by
    apply Hom.ext; funext z
    calc x.inv.f z = x.inv.f (y.hom.f (y.inv.f z)) := by rw [y.hom_inv]
      _ = x.inv.f (x.hom.f (y.inv.f z)) := by rw [h]
      _ = y.inv.f z := x.inv_hom
  exact Iso.ext h hi
-- `Iris.Chain.cauchy` (hypothesis 5): necessary, CS chain escC (true at i+1): elements 0 and 1 differ at index 1
theorem w3c1_83 : ¬ drop0% Iris.Chain.cauchy 5 := fun h => by
  have := @h CS _ escC 1 0 1 (Nat.le_refl 1)
  simp [escC] at this
-- `Iris.Chain.chain_none_const` (hypothesis 4): necessary, the constant chain some ()
theorem w3c1_84 : ¬ drop0% Iris.Chain.chain_none_const 4 := fun h =>
  nomatch congrArg (fun c : Chain (Option Unit) => c.chain 0) (@h Unit 0 _ (Chain.const (some ())))
-- `Iris.Chain.chain_option_some` (hypothesis 5): necessary, the constant chain none is no lift of a chain by some
theorem w3c1_85 : ¬ drop0% Iris.Chain.chain_option_some 5 := fun h => by
  obtain ⟨c', e⟩ := @h Unit 0 () _ (Chain.const none)
  exact nomatch congrArg (fun c : Chain (Option Unit) => c.chain 0) e
-- `Iris.COFE.conv_compl'` (hypothesis 5): necessary, CS chain escC: limit all false, element 0 true at 1
theorem w3c1_86 : ¬ drop0% Iris.COFE.conv_compl' 5 := fun h => by
  have := @h CS _ escC 1 0 1 (Nat.le_refl 1)
  simp [cs_compl, escC] at this
-- `Iris.COFE.discrete_cofe_compl` (hypothesis 2): necessary, CS chain escC: limit all false, element 0 true at 1
theorem w3c1_87 : ¬ drop0% Iris.COFE.discrete_cofe_compl 2 := fun h => by
  have := congrArg (fun x : CS => x.s 1) (@h CS _ escC)
  simp [cs_compl, escC] at this
-- `Iris.COFE.OFunctorContractive.map_distLater` (hypothesis 15): necessary, F = ▶ (A -n> B), n = 1, f1 = const cT, f2 = const cF : Unit -n> CS, g = id
theorem w3c1_88 : ¬ drop0% Iris.COFE.OFunctorContractive.map_distLater 15 := fun h => by
  have := @h CS Unit CS CS (LaterOF (HomOF IdOF IdOF)) _ _ _ _ _ 1 (Hom.const cT) (Hom.const cF)
    Hom.id Hom.id DistLater.rfl (Later.next Hom.id)
  exact cTF0 ((this 0 (by omega)) ())
-- `Iris.Option.map_ne` (hypothesis 9): necessary, f = id, g = const 1, x = y = some 0
theorem w3c1_89 : ¬ drop0% Iris.Option.map_ne 9 := fun h =>
  tn01 (@h TN _ TN _ id (fun _ => ⟨1⟩) (some ⟨0⟩) (some ⟨0⟩) 0 Dist.rfl)
-- `Iris.Option.bind_ne` (hypothesis 9): necessary, f = some, g = const (some 1), x = y = some 0
theorem w3c1_90 : ¬ drop0% Iris.Option.bind_ne 9 := fun h =>
  tn01 (@h TN _ TN _ some (fun _ => some ⟨1⟩) (some ⟨0⟩) (some ⟨0⟩) 0 Dist.rfl)
-- `Iris.Option.bind_ne` (hypothesis 10): necessary, f = g = some, x = some 0, y = some 1
theorem w3c1_91 : ¬ drop0% Iris.Option.bind_ne 10 := fun h =>
  tn01 (@h TN _ TN _ some some (some ⟨0⟩) (some ⟨1⟩) 0 (fun _ _ hxy => hxy))
-- `Iris.instNonExpansiveProdMap` (hypothesis 10): necessary, f = bad, g = id
theorem w3c1_92 : ¬ drop0% Iris.instNonExpansiveProdMap 10 := fun h =>
  bad_not_ne ((@h TN TN TN TN _ _ _ _ bad id id_ne).ne (x₁ := (⟨1⟩, ⟨0⟩)) (x₂ := (⟨2⟩, ⟨0⟩)) ⟨tn12, Dist.rfl⟩).1
-- `Iris.instNonExpansiveProdMap` (hypothesis 11): necessary, f = id, g = bad
theorem w3c1_93 : ¬ drop0% Iris.instNonExpansiveProdMap 11 := fun h =>
  bad_not_ne ((@h TN TN TN TN _ _ _ _ id bad id_ne).ne (x₁ := (⟨0⟩, ⟨1⟩)) (x₂ := (⟨0⟩, ⟨2⟩)) ⟨Dist.rfl, tn12⟩).2
-- `Iris.instNonExpansiveSumMap` (hypothesis 10): necessary, f = bad, g = id, at inl
theorem w3c1_94 : ¬ drop0% Iris.instNonExpansiveSumMap 10 := fun h =>
  bad_not_ne ((@h TN TN TN TN _ _ _ _ bad id id_ne).ne (x₁ := .inl ⟨1⟩) (x₂ := .inl ⟨2⟩) tn12)
-- `Iris.instNonExpansiveSumMap` (hypothesis 11): necessary, f = id, g = bad, at inr
theorem w3c1_95 : ¬ drop0% Iris.instNonExpansiveSumMap 11 := fun h =>
  bad_not_ne ((@h TN TN TN TN _ _ _ _ id bad id_ne).ne (x₁ := .inr ⟨1⟩) (x₂ := .inr ⟨2⟩) tn12)
-- `Iris.Sum.map_ext` (hypothesis 9): necessary, x = inl true, f = id, f' = not
theorem w3c1_96 : ¬ drop0% Iris.Sum.map_ext 9 := fun h => by
  have := @h Bool Bool Bool Bool (.inl true) id not id id (fun _ => rfl)
  simp at this
-- `Iris.Sum.map_ext` (hypothesis 10): necessary, x = inr true, g = id, g' = not
theorem w3c1_97 : ¬ drop0% Iris.Sum.map_ext 10 := fun h => by
  have := @h Bool Bool Bool Bool (.inr true) id id id not (fun _ => rfl)
  simp at this
-- `Iris.Sum.map_ne` (hypothesis 13): necessary, x = inr (), g = const 0, g' = const 1 in TN
theorem w3c1_98 : ¬ drop0% Iris.Sum.map_ne 13 := fun h =>
  tn01 (@h Unit TN Unit TN _ _ 0 (.inr ()) (fun _ => ⟨0⟩) (fun _ => ⟨0⟩) (fun _ => ⟨0⟩) (fun _ => ⟨1⟩) (fun _ => Dist.rfl))
-- `Iris.LimitPreserving.compl` (hypothesis 5): necessary, discrete DB, P = (· = true), constant chain false
theorem w3c1_99 : ¬ drop0% Iris.LimitPreserving.compl 5 := fun h => by
  have := @h DB _ (fun x => x = ⟨true⟩) (db_lp _) (Chain.const ⟨false⟩)
  rw [COFE.compl_const] at this
  cases this
-- `Iris.LimitPreserving.discrete` (hypothesis 3): necessary, CS, P = has some true (chain escC)
theorem w3c1_100 : ¬ drop0% Iris.LimitPreserving.discrete 3 := fun h =>
  hasT_not_lp (@h CS _ hasT)
-- `Iris.LimitPreserving.and` (hypothesis 4): necessary, P = hasT on CS, Q = True
theorem w3c1_101 : ¬ drop0% Iris.LimitPreserving.and 4 := fun h =>
  hasT_not_lp (LimitPreserving.ext (fun {_} => ⟨And.left, fun hx => ⟨hx, trivial⟩⟩)
    (@h CS _ hasT (fun _ => True) LimitPreserving.const))
-- `Iris.LimitPreserving.and` (hypothesis 5): necessary, P = True, Q = hasT on CS
theorem w3c1_102 : ¬ drop0% Iris.LimitPreserving.and 5 := fun h =>
  hasT_not_lp (LimitPreserving.ext (fun {_} => ⟨And.right, fun hx => ⟨trivial, hx⟩⟩)
    (@h CS _ (fun _ => True) hasT LimitPreserving.const))
-- `Iris.LimitPreserving.forall` (hypothesis 4): necessary, beta = True, P _ = hasT on CS
theorem w3c1_103 : ¬ drop0% Iris.LimitPreserving.forall 4 := fun h =>
  hasT_not_lp (LimitPreserving.ext (fun {_} => ⟨fun hx => hx trivial, fun hx _ => hx⟩)
    (@h CS True _ (fun _ => hasT)))
-- `Iris.LimitPreserving.impl` (hypothesis 4): necessary, CS, P1 = no true, P2 = False: (P1 → False) is hasT
theorem w3c1_104 : ¬ drop0% Iris.LimitPreserving.impl 4 := fun h =>
  hasT_not_lp (LimitPreserving.ext (fun {_} => ⟨fun hx => Classical.byContradiction hx, fun hx hn => hn hx⟩)
    (@h CS _ (fun x => ¬ hasT x) (fun _ => False) LimitPreserving.const))
-- `Iris.LimitPreserving.impl` (hypothesis 5): necessary, CS, P1 = True, P2 = hasT
theorem w3c1_105 : ¬ drop0% Iris.LimitPreserving.impl 5 := fun h =>
  hasT_not_lp (LimitPreserving.ext (fun {_} => ⟨fun hx => hx trivial, fun hx _ => hx⟩)
    (@h CS _ (fun _ => True) hasT (fun _ hx => hx)))
-- `Iris.LimitPreserving.impl'` (hypothesis 4): necessary, CS, P1 = no true, P2 = False
theorem w3c1_106 : ¬ drop0% Iris.LimitPreserving.impl' 4 := fun h =>
  hasT_not_lp (LimitPreserving.ext (fun {_} => ⟨fun hx => Classical.byContradiction hx, fun hx hn => hn hx⟩)
    (@h CS _ (fun x => ¬ hasT x) (fun _ => False) LimitPreserving.const))
-- `Iris.LimitPreserving.impl'` (hypothesis 5): necessary, CS, P1 = True, P2 = hasT
theorem w3c1_107 : ¬ drop0% Iris.LimitPreserving.impl' 5 := fun h =>
  hasT_not_lp (LimitPreserving.ext (fun {_} => ⟨fun hx => hx trivial, fun hx _ => hx⟩)
    (@h CS _ (fun _ => True) hasT (fun _ => Iff.rfl)))
-- `Iris.LimitPreserving.ext` (hypothesis 4): necessary, CS, P = True, Q = hasT
theorem w3c1_108 : ¬ drop0% Iris.LimitPreserving.ext 4 := fun h =>
  hasT_not_lp (@h CS _ (fun _ => True) hasT LimitPreserving.const)
-- `Iris.LimitPreserving.ext` (hypothesis 5): necessary, CS, P = Q = hasT
theorem w3c1_109 : ¬ drop0% Iris.LimitPreserving.ext 5 := fun h =>
  hasT_not_lp (@h CS _ hasT hasT Iff.rfl)
-- `Iris.fixpoint_unique` (hypothesis 5): necessary, DB, f = const true, x = false
theorem w3c1_110 : ¬ drop0% Iris.fixpoint_unique 5 := fun h =>
  nomatch ((@h DB _ _ (cst true) ⟨false⟩).trans (fix_cst true))
-- `Iris.fixpoint_dist` (hypothesis 5): necessary, CS, f = z0 (index 0 zeroed) is 0-close to the contractive shift but not contractive
theorem w3c1_111 : ¬ indep0% Iris.fixpoint_dist 5 := fun h =>
  z0_not_contr (@h CS _ _ z0 shift shiftC 0 z0_shift)
-- `Iris.fixpoint_dist` (hypothesis 6): necessary, CS, f = shift, g = z0
theorem w3c1_112 : ¬ indep0% Iris.fixpoint_dist 6 := fun h =>
  z0_not_contr (@h CS _ _ shift z0 shiftC 0 (fun z => (z0_shift z).symm))
-- `Iris.fixpoint_dist` (hypothesis 8): necessary, DB, f = const true, g = const false
theorem w3c1_113 : ¬ drop0% Iris.fixpoint_dist 8 := fun h => by
  have := @h DB _ _ (fun _ => ⟨true⟩) (fun _ => ⟨false⟩) _ _ 0
  rw [fixc, fixc] at this
  cases this
-- `Iris.fixpoint_proper` (hypothesis 5): removable, the equation hypothesis makes f = g, so Contractive f is Contractive g
theorem w3c1_114 : indep% Iris.fixpoint_proper 5 := by
  intro α _ _ f g hg H
  have e : f = g := funext H
  subst e; exact hg
-- `Iris.fixpoint_proper` (hypothesis 6): removable, the equation hypothesis makes f = g, so Contractive g is Contractive f
theorem w3c1_115 : indep% Iris.fixpoint_proper 6 := by
  intro α _ _ f g hf H
  have e : f = g := funext H
  subst e; exact hf
-- `Iris.fixpoint_proper` (hypothesis 7): necessary, DB, f = const true, g = const false
theorem w3c1_116 : ¬ drop0% Iris.fixpoint_proper 7 := fun h => by
  have := @h DB _ _ (fun _ => ⟨true⟩) (fun _ => ⟨false⟩) _ _
  rw [fixc, fixc] at this
  cases this
-- `Iris.OFE.ContractiveHom.fixpoint_ind` (hypothesis 6): necessary, P = False
theorem w3c1_117 : ¬ drop0% Iris.OFE.ContractiveHom.fixpoint_ind 6 := fun h =>
  @h DB _ _ (cst true) (fun _ => False) default (fun _ hx => hx) LimitPreserving.const
-- `Iris.OFE.ContractiveHom.fixpoint_ind` (hypothesis 7): necessary, DB, f = const true, P = (· = false), x = false
theorem w3c1_118 : ¬ drop0% Iris.OFE.ContractiveHom.fixpoint_ind 7 := fun h => by
  have := @h DB _ _ (cst true) (fun x => x = ⟨false⟩) ⟨false⟩ rfl (db_lp _)
  have e : ContractiveHom.fixpoint (cst true) = ⟨true⟩ := fix_cst true
  rw [e] at this
  cases this
-- `Iris.OFE.ContractiveHom.fixpoint_ind` (hypothesis 8): necessary, CS, f = shift (fixpoint all false), P = hasT, x = all true
theorem w3c1_119 : ¬ drop0% Iris.OFE.ContractiveHom.fixpoint_ind 8 := fun h => by
  have := @h CS _ _ shift.toContractiveHom hasT cT ⟨0, rfl⟩ (fun _ ⟨k, hk⟩ => ⟨k+1, hk⟩)
  have e : ContractiveHom.fixpoint shift.toContractiveHom = cF :=
    (fixpoint_unique (f := shift.toContractiveHom) shift_cF).symm
  rw [e] at this
  exact not_hasT_cF this
-- `Iris.repeat_dist` (hypothesis 4): necessary, TN, rf and rg 0-close pointwise, second iterates at 3 are 0 and 1
theorem w3c1_120 : ¬ drop0% Iris.repeat_dist 4 := fun h => by
  have := @h TN _ rf rg 0 rf_rg 2 ⟨3⟩
  simp [Nat.repeat, rf, rg, tn_dist] at this
-- `Iris.fixpointK_unfold` (hypothesis 5): necessary, CS, k = 0: the identity is not contractive
theorem w3c1_121 : ¬ indep0% Iris.fixpointK_unfold 5 := fun h =>
  id_not_contr (@h CS _ _ 0 id)
-- `Iris.fixpointK_unique` (hypothesis 5): necessary, CS, k = 0, f = id
theorem w3c1_122 : ¬ indep0% Iris.fixpointK_unique 5 := fun h =>
  id_not_contr (@h CS _ _ 0 id cT rfl)
-- `Iris.fixpointK_unique` (hypothesis 7): necessary, DB, k = 1, f = const true, x = false
theorem w3c1_123 : ¬ drop0% Iris.fixpointK_unique 7 := fun h =>
  nomatch ((@h DB _ _ 1 (fun _ => ⟨true⟩) (rc1 true) ⟨false⟩).trans (fixK1 true))
-- `Iris.fixpointK_ne` (hypothesis 6): necessary, CS, k = 1, f = z0 (non-expansive, not contractive), g = shift
theorem w3c1_124 : ¬ indep0% Iris.fixpointK_ne 6 := fun h =>
  z0_not_contr ⟨fun hd => (@h CS _ _ 1 z0 shift rs1 z0NE 0 z0_shift).distLater_dist hd⟩
-- `Iris.fixpointK_ne` (hypothesis 7): necessary, CS, k = 1, f = shift, g = z0
theorem w3c1_125 : ¬ indep0% Iris.fixpointK_ne 7 := fun h =>
  z0_not_contr ⟨fun hd => (@h CS _ _ 1 shift z0 rs1 inferInstance 0 (fun z => (z0_shift z).symm)).distLater_dist hd⟩
-- `Iris.fixpointK_ne` (hypothesis 8): necessary, CS, k = 2, kf/kg 0-close (not non-expansive), second iterates constant with fixpoints differing at index 0
theorem w3c1_126 : ¬ drop0% Iris.fixpointK_ne 8 := fun h => by
  have d := @h CS _ _ 2 kf kg kfC kgC 0 (fun z k hk => by
    have : k = 0 := by omega
    subst this; rfl) 0 (Nat.le_refl 0)
  have hp := fixpointK_unfold (α := CS) 2 kf
  have hq := fixpointK_unfold (α := CS) 2 kg
  have p1 : (fixpointK 2 kf).s 1 = true := by
    have := congrArg (fun x => x.s 1) hp; simpa [kf] using this
  have p0 : (fixpointK 2 kf).s 0 = true := by
    have := congrArg (fun x => x.s 0) hp; simp [kf] at this; rw [this, p1]
  have q1 : (fixpointK 2 kg).s 1 = false := by
    have := congrArg (fun x => x.s 1) hq; simpa [kg] using this
  have q0 : (fixpointK 2 kg).s 0 = false := by
    have := congrArg (fun x => x.s 0) hq; simp [kg] at this; rw [this, q1]
  rw [p0, q0] at d
  cases d
-- `Iris.fixpointK_ne` (hypothesis 10): necessary, DB, k = 1, f = const true, g = const false
theorem w3c1_127 : ¬ drop0% Iris.fixpointK_ne 10 := fun h => by
  have := @h DB _ _ 1 (fun _ => ⟨true⟩) (fun _ => ⟨false⟩) (rc1 true) (rc1 false) inferInstance 0
  have e : (fixpointK 1 (fun _ : DB => (⟨true⟩ : DB)) : DB) = fixpointK 1 (fun _ : DB => (⟨false⟩ : DB)) := this
  rw [fixK1, fixK1] at e
  cases e
-- `Iris.fixpointK_proper` (hypothesis 6): removable, the equation hypothesis makes f = g
theorem w3c1_128 : indep% Iris.fixpointK_proper 6 := by
  intro α _ _ k f g hg _ H
  have e : f = g := funext H
  subst e; exact hg
-- `Iris.fixpointK_proper` (hypothesis 7): removable, the equation hypothesis makes f = g
theorem w3c1_129 : indep% Iris.fixpointK_proper 7 := by
  intro α _ _ k f g hf _ H
  have e : f = g := funext H
  subst e; exact hf
-- `Iris.fixpointK_proper` (hypothesis 9): necessary, DB, k = 1, f = const true, g = const false
theorem w3c1_130 : ¬ drop0% Iris.fixpointK_proper 9 := fun h => by
  have := @h DB _ _ 1 (fun _ => ⟨true⟩) (fun _ => ⟨false⟩) (rc1 true) (rc1 false) inferInstance
  rw [fixK1, fixK1] at this
  cases this
-- `Iris.fixpointK_ind` (hypothesis 5): necessary, CS, k = 0, f = id, P = True
theorem w3c1_131 : ¬ indep0% Iris.fixpointK_ind 5 := fun h =>
  id_not_contr (@h CS _ _ 0 id (fun _ => True) cT trivial (fun _ _ => trivial) LimitPreserving.const)
-- `Iris.fixpointK_ind` (hypothesis 8): necessary, P = False
theorem w3c1_132 : ¬ drop0% Iris.fixpointK_ind 8 := fun h =>
  @h DB _ _ 1 (fun _ => ⟨true⟩) (rc1 true) (fun _ => False) default (fun _ hx => hx) LimitPreserving.const
-- `Iris.fixpointK_ind` (hypothesis 9): necessary, DB, k = 1, f = const true, P = (· = false), x = false
theorem w3c1_133 : ¬ drop0% Iris.fixpointK_ind 9 := fun h => by
  have := @h DB _ _ 1 (fun _ => ⟨true⟩) (rc1 true) (fun x => x = ⟨false⟩) ⟨false⟩ rfl (db_lp _)
  rw [fixK1] at this
  cases this
-- `Iris.fixpointK_ind` (hypothesis 10): necessary, CS, k = 1, f = shift (fixpoint all false), P = hasT, x = all true
theorem w3c1_134 : ¬ drop0% Iris.fixpointK_ind 10 := fun h => by
  have := @h CS _ _ 1 shift rs1 hasT cT ⟨0, rfl⟩ (fun _ ⟨k, hk⟩ => ⟨k+1, hk⟩)
  rw [← fixpointK_unique 1 shift shift_cF] at this
  exact not_hasT_cF this
-- `Iris.fixpointA_unique` (hypothesis 10): necessary, DB, fA = fB = const true (fixpointA = true), p = false, q = true
theorem w3c1_135 : ¬ drop0% Iris.fixpointA_unique 10 := fun h =>
  nomatch ((@h DB DB ⟨false⟩ ⟨true⟩ _ _ _ _ (fAc true) (fBc true) rfl).trans
    (fixpointA_unique (p := ⟨true⟩) (q := ⟨true⟩) (fAc true) (fBc true) rfl rfl).symm)
-- `Iris.fixpointA_unique` (hypothesis 11): necessary, DB, fA x y = y, fB = const true (fixpointA = true), p = q = false
theorem w3c1_136 : ¬ drop0% Iris.fixpointA_unique 11 := fun h =>
  nomatch ((@h DB DB ⟨false⟩ ⟨false⟩ _ _ _ _ fAid (fBc true) rfl).trans
    (fixpointA_unique (p := ⟨true⟩) (q := ⟨true⟩) fAid (fBc true) rfl rfl).symm)
-- `Iris.fixpointB_unique` (hypothesis 10): necessary, CS, fA = const cT, fB x y = shift x (fixpointB = shift cT), p = q = all false
theorem w3c1_137 : ¬ drop0% Iris.fixpointB_unique 10 := fun h => by
  have e := (@h CS CS cF cF _ _ _ _ (gAc cT) gBs shift_cF.symm).trans
    (fixpointB_unique (p := cT) (q := shift cT) (gAc cT) gBs rfl rfl).symm
  have := congrArg (fun x => x.s 1) e
  simp [cF, cT, shift] at this
-- `Iris.fixpointB_unique` (hypothesis 11): necessary, DB, fA = fB = const true (fixpointB = true), p = true, q = false
theorem w3c1_138 : ¬ drop0% Iris.fixpointB_unique 11 := fun h =>
  nomatch ((@h DB DB ⟨true⟩ ⟨false⟩ _ _ _ _ (fAc true) (fBc true) rfl).trans
    (fixpointB_unique (p := ⟨true⟩) (q := ⟨true⟩) (fAc true) (fBc true) rfl rfl).symm)
-- `Iris.fixpointA_proper` (hypothesis 10): necessary, DB, fA = const true vs fA' = const false, fB = fB' = const true
theorem w3c1_139 : ¬ drop0% Iris.fixpointA_proper 10 := fun h =>
  nomatch ((fixpointA_unique (p := ⟨true⟩) (q := ⟨true⟩) (fAc true) (fBc true) rfl rfl).trans
    ((@h DB DB _ _ _ _ (fAc true) (fAc false) (fBc true) (fBc true) (fun _ _ => rfl)).trans
    (fixpointA_unique (p := ⟨false⟩) (q := ⟨true⟩) (fAc false) (fBc true) rfl rfl).symm))
-- `Iris.fixpointA_proper` (hypothesis 11): necessary, DB, fA = fA' = (x, y ↦ y), fB = const true vs fB' = const false
theorem w3c1_140 : ¬ drop0% Iris.fixpointA_proper 11 := fun h =>
  nomatch ((fixpointA_unique (p := ⟨true⟩) (q := ⟨true⟩) fAid (fBc true) rfl rfl).trans
    ((@h DB DB _ _ _ _ fAid fAid (fBc true) (fBc false) (fun _ _ => rfl)).trans
    (fixpointA_unique (p := ⟨false⟩) (q := ⟨false⟩) fAid (fBc false) rfl rfl).symm))
-- `Iris.fixpointB_proper` (hypothesis 10): necessary, CS, fA = const cT vs const cF, fB = fB' = (x, y ↦ shift x): fixpointB = shift cT vs shift cF
theorem w3c1_141 : ¬ drop0% Iris.fixpointB_proper 10 := fun h => by
  have e := (fixpointB_unique (p := cT) (q := shift cT) (gAc cT) gBs rfl rfl).trans
    ((@h CS CS _ _ _ _ (gAc cT) (gAc cF) gBs gBs (fun _ _ => rfl)).trans
    (fixpointB_unique (p := cF) (q := shift cF) (gAc cF) gBs rfl rfl).symm)
  have := congrArg (fun x => x.s 1) e
  simp [cF, cT, shift] at this
-- `Iris.fixpointB_proper` (hypothesis 11): necessary, DB, fA = fA' = const true, fB = const true vs fB' = const false
theorem w3c1_142 : ¬ drop0% Iris.fixpointB_proper 11 := fun h =>
  nomatch ((fixpointB_unique (p := ⟨true⟩) (q := ⟨true⟩) (fAc true) (fBc true) rfl rfl).trans
    ((@h DB DB _ _ _ _ (fAc true) (fAc true) (fBc true) (fBc false) (fun _ _ => rfl)).trans
    (fixpointB_unique (p := ⟨true⟩) (q := ⟨false⟩) (fAc true) (fBc false) rfl rfl).symm))
-- `Iris.laterMap_ext` (hypothesis 7): necessary, DB, f = const true, g = const false
theorem w3c1_143 : ¬ drop0% Iris.laterMap_ext 7 := fun h =>
  nomatch congrArg Later.car (@h DB DB _ _ (Hom.const ⟨true⟩) (Hom.const ⟨false⟩) (Later.next ⟨true⟩))
-- `Iris.OFE.cast_dist` (hypothesis 7): necessary, alpha = Unit, beta = DB are different types
theorem w3c1_144 : ¬ indep0% Iris.OFE.cast_dist 7 := fun h => by
  have e := @h Unit DB 0 _ _ () () Dist.rfl
  have key : ∀ (T : Type), Unit = T → ∀ a b : T, a = b := by
    intro T hT; subst hT; intro a b; rfl
  exact nomatch key DB e ⟨true⟩ ⟨false⟩
-- `Iris.OFE.cast_dist` (hypothesis 8): necessary, TN with its own OFE vs the discrete OFE on TN, Ht = rfl, 1 vs 2
theorem w3c1_145 : ¬ drop0% Iris.OFE.cast_dist 8 := fun h =>
  tn12ne (@h TN TN 0 tnOFE (OFE.ofDiscrete TN) ⟨1⟩ ⟨2⟩ rfl tn12)
-- `Iris.OFE.cast_dist` (hypothesis 9): necessary, TN, Ht = rfl, 0 vs 1
theorem w3c1_146 : ¬ drop0% Iris.OFE.cast_dist 9 := fun h =>
  tn01 (@h TN TN 0 tnOFE tnOFE ⟨0⟩ ⟨1⟩ rfl rfl)
