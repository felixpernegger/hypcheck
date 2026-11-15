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
namespace W5c0
open Iris Iris.BI Iris.Std Iris.Instances.Classical Iris.Instances.Data

-- helper: step-indexed prop true only at step 0 (not timeless)
def s0 : SiProp := ⟨fun n => n = 0, fun h hle => by omega⟩

-- helper: a SiProp holding at 0 but not at 1 is not timeless
theorem nt {Q : SiProp} (h : iprop(▷ Q) ⊢ iprop(◇ Q)) (h0 : Q.holds 0) (h1 : ¬ Q.holds 1) : False := by
  rcases h 1 h0 with h' | h'
  · exact h'
  · exact h1 h'

-- helper: non-affine HeapProp Unit
abbrev HP := Iris.Instances.Classical.HeapProp Unit
def s1 : State Unit := fun _ => result ()
theorem s1_ne : s1 ≠ ∅ := fun h => by have h0 := congrFun h 0; cases h0
theorem heap_not_affine : ¬ ((iprop(True) : HP) ⊢ emp) := fun h => s1_ne (h s1 trivial)
def h0 : State Unit := fun i => if i = 0 then result () else unknown
def own0 : HP := fun σ => σ 0 ≠ unknown
theorem own0_h0 : own0 h0 := by simp [own0, h0]
-- helper: own0 is not persistent
theorem own0_not_pers {Q : HP} (e : Q ⊢ own0) (e' : own0 ⊢ Q) (h : Q ⊢ iprop(<pers> Q)) : False :=
  (e ∅ (h h0 (e' h0 own0_h0))) rfl
-- helper: two-element UORA with equality order (copied from Probe3): UPred NA is non-affine
inductive NA | e | a deriving DecidableEq
def NA.op : NA → NA → NA
  | .e, y => y
  | .a, _ => .a
instance : OFE NA := OFE.ofDiscrete NA
instance : OFE.Discrete NA := ⟨id⟩
instance instORA : ORA NA := ORA.ofDiscreteORAData {
  pcore := fun _ => some .e
  op := NA.op
  Valid := fun _ => True
  Order := Eq
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
  pcore_op_left := by intro x cx h; cases h; cases x <;> rfl
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := fun _ _ _ => trivial
  ord_trans := fun _ _ _ h1 h2 => h1.trans h2
  op_mono_left := by intro x y z h; cases h; rfl
  valid_of_ord := fun _ _ _ _ => trivial
  pcore_mono := by intro x y cx h1 h2; exact ⟨.e, rfl, by cases h2; rfl⟩
  pcore_order_op := by intro x cx h y; exact ⟨.e, rfl, by cases h; rfl⟩
  pcore_increasing := by intro x cx h y; cases h; rfl
  increasing_closed := by intro x y _ h; cases h; assumption }
instance : OrderRefl NA := ⟨fun x => show x = x from rfl⟩
instance instUORA : UORA NA where
  unit := .e
  unit_valid := trivial
  unit_left_id := rfl
  pcore_unit := rfl

-- helper: in UPred NA, True does not entail emp
theorem na_true_not_emp : ¬ ((iprop(True) : UPred NA) ⊢ iprop(emp)) := fun h => by
  have H := h 0 ⟨.a, trivial⟩ trivial
  cases H

-- helper: in HeapProp every prop is timeless
theorem hpT (P : HP) : Timeless P := ⟨fun _ h => Or.inr h⟩

-- helper: only0 s0 holds at step 1
theorem o0s0 : (iprop(<only0> s0) : SiProp).holds 1 := by
  intro m _ hf
  cases m with
  | zero => rfl
  | succ k => exact absurd hf id
-- helper: identity embedding of any BI into itself
@[instance_reducible] def idEmb (PROP : Type _) [BI PROP] : BiEmbed PROP PROP where
  embed := id
  ne := ⟨fun _ _ _ h => h⟩
  mono := fun h => h
  emp_valid_inj := fun _ h => h
  emp_2 := .rfl
  impl_2 := fun _ _ => .rfl
  forall_2 := fun _ _ h => sForall_intro h
  exist_1 := fun _ _ h => sExists_elim h
  sep := fun _ _ => .rfl
  wand_2 := fun _ _ => .rfl
  persistently := fun _ => .rfl
theorem idEmp (PROP : Type _) [BI PROP] : @BiEmbedEmp PROP PROP _ _ (idEmb PROP) :=
  @BiEmbedEmp.mk PROP PROP _ _ (idEmb PROP) .rfl
theorem idLat (PROP : Type _) [BI PROP] : @BiEmbedLater PROP PROP _ _ (idEmb PROP) :=
  @BiEmbedLater.mk PROP PROP _ _ (idEmb PROP) (fun _ => .rfl)
theorem idSbi (PROP : Type _) [Sbi PROP] : @BiEmbedSbi PROP PROP _ _ (idEmb PROP) _ _ :=
  @BiEmbedSbi.mk PROP PROP _ _ (idEmb PROP) _ _ (fun _ => .rfl) (fun _ => .rfl)

-- helper: the siPure embedding of SiProp into any Sbi (in a non-affine Sbi it does not preserve emp)
theorem sExists_sub (Ψ : SiProp → Prop) :
    (BIBase.sExists Ψ : SiProp) ⊢ iprop(∃ x : {p : SiProp // Ψ p}, x.1) :=
  fun _ ⟨P, hP, h⟩ => SiProp.exists_holds.mpr ⟨⟨P, hP⟩, h⟩
@[instance_reducible] def spE (PROP : Type _) [Sbi PROP] : BiEmbed SiProp PROP where
  embed := siPure
  ne := Sbi.siPure_ne
  mono := siPure_mono
  emp_valid_inj := fun _ h => siPure_emp_valid.mp h
  emp_2 := true_intro.trans siPure_pure.2
  impl_2 := fun _ _ => siPure_imp_mpr
  forall_2 := fun Ψ R h =>
    (forall_intro fun q => imp_intro_swap (pure_elim_left fun hq => h q hq)).trans siPure_sForall_mpr
  exist_1 := fun Ψ R h =>
    (siPure_mono (sExists_sub Ψ)).trans (siPure_exist.mp.trans (exists_elim fun x => h x.1 x.2))
  sep := fun _ _ => siPure_and_sep
  wand_2 := fun _ _ => siPure_imp_wand.2
  persistently := fun _ => ⟨Persistent.persistent, persistently_elim⟩
theorem spT {PROP : Type _} [Sbi PROP] {P : SiProp} (hP : (iprop(True) : SiProp) ⊢ P) :
    (iprop(True) : PROP) ⊢ @Embed.embed SiProp PROP (spE PROP).toEmbed P :=
  siPure_pure.2.trans (siPure_mono hP)
theorem spTemp {PROP : Type _} [Sbi PROP] {P : SiProp} (hP : (iprop(emp) : SiProp) ⊢ P) :
    (iprop(True) : PROP) ⊢ @Embed.embed SiProp PROP (spE PROP).toEmbed P :=
  spT (fun n _ => hP n trivial)

-- helper: delay embedding of SiProp into itself (copied from Probe2); does not commute with later
def dl (P : SiProp) : SiProp := ⟨fun n => P.holds (n - 1), fun h hle => P.closed h (by omega)⟩
@[instance_reducible] def delayE : BiEmbed SiProp SiProp where
  embed := dl
  ne := ⟨fun {n x y} h m hle => h (by omega)⟩
  mono := fun h n hp => h _ hp
  emp_valid_inj := fun P h n _ => h (n + 1) trivial
  emp_2 := fun _ _ => trivial
  impl_2 := fun P Q n h m hm hp => by
    cases n with
    | zero => have e : m = 0 := by omega
              subst e; exact h 0 (Nat.le_refl 0) hp
    | succ k => exact h (m + 1) (by omega) hp
  forall_2 := fun Ψ R h n hr P hP => h P hP n hr
  exist_1 := fun Ψ R h n ⟨P, hP, hp⟩ => h P hP n hp
  sep := fun P Q => ⟨fun _ h => h, fun _ h => h⟩
  wand_2 := fun P Q n h m hm hp => by
    cases n with
    | zero => have e : m = 0 := by omega
              subst e; exact h 0 (Nat.le_refl 0) hp
    | succ k => exact h (m + 1) (by omega) hp
  persistently := fun P => ⟨fun _ h => h, fun _ h => h⟩
inductive Ix | lo | hi deriving DecidableEq, Inhabited
instance leIx : LE Ix := ⟨fun a b => a = .lo ∨ b = .hi⟩
instance : Std.IsPreorder Ix where
  le_refl a := by cases a <;> simp [LE.le]
  le_trans a b c h1 h2 := by cases a <;> cases b <;> cases c <;> simp_all [LE.le]
def I2 : BiIndex := ⟨Ix, leIx⟩
/-- the prop itself at lo and its delay at hi -/
def eD (P : SiProp) : MonPred I2 SiProp where
  monPred_at i := match i with | .lo => P | .hi => dl P
  monPred_mono {i j} h := by
    cases i <;> cases j
    · exact fun _ h => h
    · exact fun n hp => P.closed hp (by omega)
    · exact absurd h (fun h' => by rcases h' with h' | h' <;> cases h')
    · exact fun _ h => h
/-- embedding of SiProp into MonPred over I2 via eD; it does not commute with plainly -/
@[instance_reducible] def eDE : BiEmbed SiProp (MonPred I2 SiProp) where
  embed := eD
  ne := ⟨fun n x y h i => by
    cases i
    · exact h
    · exact fun {m} hm => h (show m - 1 ≤ n by omega)⟩
  mono := fun h i => by
    cases i
    · exact h
    · exact fun n hp => h _ hp
  emp_valid_inj := fun P h => h .lo
  emp_2 := fun i => by cases i <;> exact fun _ _ => trivial
  impl_2 := fun P Q i => by
    cases i
    · exact fun n h => h _ ⟨.lo, rfl⟩ n (Nat.le_refl n) (Or.inl rfl)
    · exact fun n h => delayE.impl_2 P Q n (h _ ⟨.hi, rfl⟩ n (Nat.le_refl n) (Or.inr rfl))
  forall_2 := fun Ψ R h i => by
    cases i
    · exact fun n hr P hP => h P hP .lo n hr
    · exact fun n hr P hP => h P hP .hi n hr
  exist_1 := fun Ψ R h i => by
    cases i
    · exact fun n ⟨P, hP, hp⟩ => h P hP .lo n hp
    · exact fun n ⟨P, hP, hp⟩ => h P hP .hi n hp
  sep := fun P Q => ⟨fun i => by cases i <;> exact fun _ h => h, fun i => by cases i <;> exact fun _ h => h⟩
  wand_2 := fun P Q i => by
    cases i
    · exact fun n h => h _ ⟨.lo, rfl⟩ n (Nat.le_refl n) (Or.inl rfl)
    · exact fun n h => delayE.wand_2 P Q n (h _ ⟨.hi, rfl⟩ n (Nat.le_refl n) (Or.inr rfl))
  persistently := fun P => ⟨fun i => by cases i <;> exact fun _ h => h, fun i => by cases i <;> exact fun _ h => h⟩
-- helper: identity basic update on SiProp (copied from Probe4) and except-0 as a second lawful basic update
@[instance_reducible] def idBupd : BIUpdate SiProp where
  bupd P := P
  bupd_ne := ⟨fun _ _ _ h => h⟩
  intro := fun _ h => h
  mono h := h
  trans := fun _ h => h
  frame_right := fun _ h => h
@[instance_reducible] def exBupd : BIUpdate SiProp where
  bupd P := iprop(◇ P)
  bupd_ne := except0_ne
  intro := except0_intro
  mono := except0_mono
  trans := except0_idem.1
  frame_right := except0_frame_right
theorem idBU (B : BIUpdate SiProp) : @BiEmbedBUpd SiProp SiProp _ _ (idEmb _) B B :=
  @BiEmbedBUpd.mk SiProp SiProp _ _ (idEmb _) B B (fun _ => .rfl)

-- `Iris.BI.later_congr` idx 4: necessary
theorem w5c0_1 : ¬ drop0% Iris.BI.later_congr 4 := fun h =>
  (@h SiProp _ iprop(True) iprop(False)).1 1 trivial
-- `Iris.BI.later_persistent` idx 3: necessary
theorem w5c0_6 : ¬ drop0% Iris.BI.later_persistent 3 := fun h =>
  own0_not_pers (fun _ h => h) (fun _ h => h) (@h HP _ own0).persistent
-- `Iris.BI.later_absorbing` idx 3: necessary
theorem w5c0_7 : ¬ drop0% Iris.BI.later_absorbing 3 := fun h =>
  heap_not_affine ((sep_emp.2.trans (sep_mono_right later_intro)).trans (@h HP _ iprop(emp)).absorbing)
-- `Iris.BI.loeb` idx 2: necessary
theorem w5c0_9 : ¬ drop0% Iris.BI.loeb 2 := fun h =>
  (@h HP _ iprop(False)) ∅ (fun x => x)
-- `Iris.BI.loeb_weak_of_strong` idx 3: necessary
theorem w5c0_10 : ¬ drop0% Iris.BI.loeb_weak_of_strong 3 := fun h =>
  (@h HP _ iprop(False) (fun _ h => h)) ∅ trivial
-- `Iris.BI.loeb_weak_of_strong` idx 4: necessary
theorem w5c0_11 : ¬ drop0% Iris.BI.loeb_weak_of_strong 4 := fun h =>
  (@h SiProp _ iprop(False) (fun _ => loeb)) 0 trivial
-- `Iris.BI.loeb_wand_intuitionistically` idx 2: necessary
theorem w5c0_12 : ¬ drop0% Iris.BI.loeb_wand_intuitionistically 2 := fun h =>
  (@h HP _ iprop(False)) ∅ ⟨rfl, fun _ _ h => h.2.elim⟩
-- `Iris.BI.loeb_wand` idx 2: necessary
theorem w5c0_13 : ¬ drop0% Iris.BI.loeb_wand 2 := fun h =>
  (@h HP _ iprop(False)) ∅ ⟨rfl, fun _ _ h => h⟩
-- `Iris.BI.later_contractive_bi_loeb` idx 2: necessary
theorem w5c0_14 : ¬ drop0% Iris.BI.later_contractive_bi_loeb 2 := fun h =>
  (@h HP _).loeb_weak (P := iprop(False)) (fun _ h => h) ∅ trivial
-- `Iris.BI.not_not_later_False` idx 2: necessary
theorem w5c0_15 : ¬ drop0% Iris.BI.not_not_later_False 2 := fun h =>
  (@h HP _) ∅ rfl (fun h => h)
-- `Iris.BI.bi_affine_alt_later_emp` idx 2: necessary
theorem w5c0_16 : ¬ drop0% Iris.BI.bi_affine_alt_later_emp 2 := fun h =>
  heap_not_affine (((@h HP _).2 (fun _ h => h)).affine iprop(True)).affine
-- `Iris.BI.laterN_mono` idx 5: necessary
theorem w5c0_18 : ¬ drop0% Iris.BI.laterN_mono 5 := fun h =>
  (@h SiProp _ 0 iprop(True) iprop(False)) 0 trivial
-- `Iris.BI.laterN_congr` idx 5: necessary
theorem w5c0_19 : ¬ drop0% Iris.BI.laterN_congr 5 := fun h =>
  (@h SiProp _ iprop(True) iprop(False) 0).1 0 trivial
-- `Iris.BI.laterN_le` idx 5: necessary
theorem w5c0_20 : ¬ drop0% Iris.BI.laterN_le 5 := fun h =>
  (@h SiProp _ 1 0 iprop(False)) 0 trivial
-- `Iris.BI.laterN_persistent` idx 4: necessary
theorem w5c0_21 : ¬ drop0% Iris.BI.laterN_persistent 4 := fun h =>
  own0_not_pers (fun _ h => h) (fun _ h => h) (@h HP _ 0 own0).persistent
-- `Iris.BI.laterN_absorbing` idx 4: necessary
theorem w5c0_22 : ¬ drop0% Iris.BI.laterN_absorbing 4 := fun h =>
  heap_not_affine (sep_emp.2.trans (@h HP _ 0 iprop(emp)).absorbing)
-- `Iris.BI.except0_mono` idx 4: necessary
theorem w5c0_23 : ¬ drop0% Iris.BI.except0_mono 4 := fun h =>
  ((@h SiProp _ iprop(True) iprop(False)) 1 (.inr trivial)).elim id id
-- `Iris.BI.except0_congr` idx 4: necessary
theorem w5c0_24 : ¬ drop0% Iris.BI.except0_congr 4 := fun h =>
  ((@h SiProp _ iprop(True) iprop(False)).1 1 (.inr trivial)).elim id id
-- `Iris.BI.except0_persistent` idx 3: necessary
theorem w5c0_30 : ¬ drop0% Iris.BI.except0_persistent 3 := fun h =>
  own0_not_pers (fun _ h => h.elim False.elim id) (fun _ h => .inr h) (@h HP _ own0).persistent
-- `Iris.BI.except0_absorbing` idx 3: necessary
theorem w5c0_31 : ¬ drop0% Iris.BI.except0_absorbing 3 := fun h =>
  s1_ne ((((sep_emp.2.trans (sep_mono_right except0_intro)).trans (@h HP _ iprop(emp)).absorbing) s1 trivial).elim False.elim id)
-- `Iris.BI.only0_mono` idx 4: necessary
theorem w5c0_33 : ¬ drop0% Iris.BI.only0_mono 4 := fun h =>
  (@h SiProp _ iprop(True) iprop(False)) 0 (fun _ _ _ => trivial) 0 (Nat.le_refl 0) trivial
-- `Iris.BI.only0_congr` idx 4: necessary
theorem w5c0_34 : ¬ drop0% Iris.BI.only0_congr 4 := fun h =>
  (@h SiProp _ iprop(True) iprop(False)).1 0 (fun _ _ _ => trivial) 0 (Nat.le_refl 0) trivial

-- `Iris.BI.later_emp` idx 2: necessary
theorem w5c0_2 : ¬ drop0% Iris.BI.later_emp 2 := fun h => by
  have H := (@h (UPred NA) _).1 0 ⟨.a, trivial⟩ trivial
  cases H
-- `Iris.BI.later_affinely` idx 2: necessary
theorem w5c0_3 : ¬ drop0% Iris.BI.later_affinely 2 := fun h => by
  have H := ((@h (UPred NA) _ iprop(True)).2 0 ⟨.a, trivial⟩ trivial).1
  cases H
-- `Iris.BI.later_intuitionistically` idx 2: necessary
theorem w5c0_4 : ¬ drop0% Iris.BI.later_intuitionistically 2 := fun h => by
  have H := ((@h (UPred NA) _ iprop(True)).2 0 ⟨.a, trivial⟩ trivial).1
  cases H
-- `Iris.BI.later_intuitionisticallyIf` idx 3: necessary
theorem w5c0_5 : ¬ drop0% Iris.BI.later_intuitionisticallyIf 3 := fun h => by
  have H := ((@h (UPred NA) _ true iprop(True)).2 0 ⟨.a, trivial⟩ trivial).1
  cases H
-- `Iris.BI.bi_later_monoid_sep_homomorphism` idx 2: necessary
theorem w5c0_8 : ¬ drop0% Iris.BI.bi_later_monoid_sep_homomorphism 2 := fun h => by
  have e := (@h (UPred NA) _).map_unit
  have H : (iprop(▷ emp) : UPred NA).holds 0 ⟨.a, trivial⟩ := trivial
  rw [e] at H
  cases H
-- `Iris.BI.except0_emp` idx 2: necessary
theorem w5c0_25 : ¬ drop0% Iris.BI.except0_emp 2 := fun h => by
  have H := (@h (UPred NA) _).1 0 ⟨.a, trivial⟩ (Or.inl trivial)
  cases H
-- `Iris.BI.bi_except0_sep_homomorphism` idx 2: necessary
theorem w5c0_32 : ¬ drop0% Iris.BI.bi_except0_sep_homomorphism 2 := fun h => by
  have e := (@h (UPred NA) _).map_unit
  have H : (iprop(◇ emp) : UPred NA).holds 0 ⟨.a, trivial⟩ := Or.inl trivial
  rw [e] at H
  cases H
-- `Iris.BI.timeless_alt` idx 2: necessary
theorem w5c0_36 : ¬ drop0% Iris.BI.timeless_alt 2 := fun h =>
  ((@h HP _ iprop(False)).1 (hpT _)) ∅ (fun h => h)
-- `Iris.BI.timeless_only0` idx 2: necessary
theorem w5c0_37 : ¬ drop0% Iris.BI.timeless_only0 2 := fun h =>
  (@h HP _ iprop(False) (hpT _)).1 ∅ (fun h => h)
-- `Iris.BI.timeless_only0` idx 4: necessary
theorem w5c0_38 : ¬ drop0% Iris.BI.timeless_only0 4 := fun h =>
  Nat.one_ne_zero ((@h SiProp _ _ s0).1 1 o0s0)
-- `Iris.BI.only0_elim_timeless` idx 2: necessary
theorem w5c0_39 : ¬ drop0% Iris.BI.only0_elim_timeless 2 := fun h =>
  (@h HP _ iprop(False) (hpT _)) ∅ (fun h => h)
-- `Iris.BI.only0_elim_timeless` idx 4: necessary
theorem w5c0_40 : ¬ drop0% Iris.BI.only0_elim_timeless 4 := fun h =>
  Nat.one_ne_zero ((@h SiProp _ _ s0) 1 o0s0)
-- `Iris.BI.exists_timeless` idx 4: necessary
theorem w5c0_41 : ¬ drop0% Iris.BI.exists_timeless 4 := fun h =>
  nt (@h SiProp _ Unit (fun _ => s0)).timeless
    (SiProp.exists_holds.mpr ⟨(), rfl⟩) (fun h1 => by
      obtain ⟨_, h2⟩ := SiProp.exists_holds.mp h1
      exact Nat.one_ne_zero h2)
-- `Iris.BI.and_timeless` idx 4: necessary
theorem w5c0_43 : ¬ drop0% Iris.BI.and_timeless 4 := fun h =>
  nt (@h SiProp _ s0 iprop(True) _).timeless
    ⟨rfl, trivial⟩ (fun h1 => Nat.one_ne_zero h1.1)
-- `Iris.BI.and_timeless` idx 5: necessary
theorem w5c0_44 : ¬ drop0% Iris.BI.and_timeless 5 := fun h =>
  nt (@h SiProp _ iprop(True) s0 _).timeless
    ⟨trivial, rfl⟩ (fun h1 => Nat.one_ne_zero h1.2)
-- `Iris.BI.or_timeless` idx 4: necessary
theorem w5c0_45 : ¬ drop0% Iris.BI.or_timeless 4 := fun h =>
  nt (@h SiProp _ s0 iprop(False) _).timeless
    (.inl rfl) (fun h1 => h1.elim Nat.one_ne_zero id)
-- `Iris.BI.or_timeless` idx 5: necessary
theorem w5c0_46 : ¬ drop0% Iris.BI.or_timeless 5 := fun h =>
  nt (@h SiProp _ iprop(False) s0 _).timeless
    (.inr rfl) (fun h1 => h1.elim id Nat.one_ne_zero)
-- `Iris.BI.impl_timeless` idx 5: necessary
theorem w5c0_48 : ¬ drop0% Iris.BI.impl_timeless 5 := fun h =>
  nt (@h SiProp _ _ iprop(True) s0).timeless
    (fun m hm _ => by show m = 0; omega) (fun h1 => Nat.one_ne_zero (h1 1 (Nat.le_refl 1) trivial))
-- `Iris.BI.sep_timeless` idx 4: necessary
theorem w5c0_49 : ¬ drop0% Iris.BI.sep_timeless 4 := fun h =>
  nt (@h SiProp _ s0 iprop(True) _).timeless
    ⟨rfl, trivial⟩ (fun h1 => Nat.one_ne_zero h1.1)
-- `Iris.BI.sep_timeless` idx 5: necessary
theorem w5c0_50 : ¬ drop0% Iris.BI.sep_timeless 5 := fun h =>
  nt (@h SiProp _ iprop(True) s0 _).timeless
    ⟨trivial, rfl⟩ (fun h1 => Nat.one_ne_zero h1.2)
-- `Iris.BI.wand_timeless` idx 5: necessary
theorem w5c0_52 : ¬ drop0% Iris.BI.wand_timeless 5 := fun h =>
  nt (@h SiProp _ _ iprop(True) s0).timeless
    (fun m hm _ => by show m = 0; omega) (fun h1 => Nat.one_ne_zero (h1 1 (Nat.le_refl 1) trivial))
-- `Iris.BI.wandIff_timeless` idx 5: necessary
theorem w5c0_54 : ¬ drop0% Iris.BI.wandIff_timeless 5 := fun h =>
  nt (@h SiProp _ _ s0 iprop(True) _).timeless
    ⟨fun _ _ _ => trivial, fun m hm _ => by show m = 0; omega⟩
    (fun h1 => Nat.one_ne_zero (h1.2 1 (Nat.le_refl 1) trivial))
-- `Iris.BI.wandIff_timeless` idx 6: necessary
theorem w5c0_55 : ¬ drop0% Iris.BI.wandIff_timeless 6 := fun h =>
  nt (@h SiProp _ _ iprop(True) s0 _).timeless
    ⟨fun m hm _ => by show m = 0; omega, fun _ _ _ => trivial⟩
    (fun h1 => Nat.one_ne_zero (h1.1 1 (Nat.le_refl 1) trivial))
-- `Iris.BI.persistently_timeless` idx 4: necessary
theorem w5c0_57 : ¬ drop0% Iris.BI.persistently_timeless 4 := fun h =>
  nt (Q := iprop(<pers> s0)) (@h SiProp _ _ s0).timeless
    rfl Nat.one_ne_zero
-- `Iris.BI.affinely_timeless` idx 4: necessary
theorem w5c0_59 : ¬ drop0% Iris.BI.affinely_timeless 4 := fun h =>
  nt (@h SiProp _ _ s0).timeless
    ⟨trivial, rfl⟩ (fun h1 => Nat.one_ne_zero h1.2)
-- `Iris.BI.absorbingly_timeless` idx 3: necessary
theorem w5c0_60 : ¬ drop0% Iris.BI.absorbingly_timeless 3 := fun h =>
  nt (@h SiProp _ s0).timeless
    ⟨trivial, rfl⟩ (fun h1 => Nat.one_ne_zero h1.2)
-- `Iris.BI.intuitionistically_timeless` idx 5: necessary
theorem w5c0_63 : ¬ drop0% Iris.BI.intuitionistically_timeless 5 := fun h =>
  nt (@h SiProp _ _ _ s0).timeless
    ⟨trivial, rfl⟩ (fun h1 => Nat.one_ne_zero h1.2)
-- `Iris.BI.from_option_timeless` idx 5: necessary
theorem w5c0_64 : ¬ drop0% Iris.BI.from_option_timeless 5 := fun h =>
  nt (Q := s0) (@h SiProp _ Unit (fun _ => iprop(True)) s0 _ none).timeless
    rfl Nat.one_ne_zero
-- `Iris.BI.from_option_timeless` idx 6: necessary
theorem w5c0_65 : ¬ drop0% Iris.BI.from_option_timeless 6 := fun h =>
  nt (Q := s0) (@h SiProp _ Unit (fun _ => s0) iprop(True) _ (some ())).timeless
    rfl Nat.one_ne_zero
-- `Iris.BI.timeless_laterN` idx 3: necessary
theorem w5c0_66 : ¬ drop0% Iris.BI.timeless_laterN 3 := fun h =>
  ((@h SiProp _ s0 1) 1 rfl).elim id Nat.one_ne_zero
-- `Iris.BI.only0_exists` idx 2: necessary
theorem w5c0_67 : ¬ drop0% Iris.BI.only0_exists 2 := fun h => by
  have H := (@h HP _ Empty Empty.elim).1 ∅ (fun h => h.elim)
  obtain ⟨_, ⟨a, _⟩, _⟩ := H
  exact a.elim
-- `Iris.BI.only0_pure` idx 2: necessary
theorem w5c0_69 : ¬ drop0% Iris.BI.only0_pure 2 := fun h =>
  (@h HP _ False).1 ∅ (fun h => h)
-- `Iris.BI.only0_emp` idx 2: necessary
theorem w5c0_70 : ¬ drop0% Iris.BI.only0_emp 2 := fun h =>
  s1_ne ((@h HP _ (hpT _)).1 s1 (fun h => h.elim))
-- `Iris.BI.only0_affinely` idx 2: necessary
theorem w5c0_74 : ¬ drop0% Iris.BI.only0_affinely 2 := fun h =>
  s1_ne ((@h HP _ (hpT _) iprop(True)).1 s1 (fun h => h.elim)).1

-- `Iris.BI.BiEmbed.mono` idx 7: necessary
theorem w5c0_79 : ¬ drop0% Iris.BI.BiEmbed.mono 7 := fun h =>
  (@h SiProp SiProp _ _ (idEmb _) iprop(True) iprop(False)) 0 trivial
-- `Iris.BI.BiEmbed.forall_2` idx 7: necessary
theorem w5c0_80 : ¬ drop0% Iris.BI.BiEmbed.forall_2 7 := fun h =>
  (@h SiProp SiProp _ _ (idEmb _) (fun P => P = iprop(False)) iprop(True)) 0 trivial _ rfl
-- `Iris.BI.BiEmbed.exist_1` idx 7: necessary
theorem w5c0_81 : ¬ drop0% Iris.BI.BiEmbed.exist_1 7 := fun h =>
  (@h SiProp SiProp _ _ (idEmb _) (fun P => P = iprop(True)) iprop(False)) 0 ⟨_, rfl, trivial⟩
-- `Iris.BI.BiEmbedEmp.embed_emp_1` idx 5: necessary
theorem w5c0_82 : ¬ drop0% Iris.BI.BiEmbedEmp.embed_emp_1 5 := fun h =>
  na_true_not_emp ((spT (P := iprop(emp)) (fun _ _ => trivial)).trans (@h SiProp (UPred NA) _ _ (spE _)))
-- `Iris.BI.BiEmbedLater.embed_later` idx 5: necessary
theorem w5c0_83 : ¬ drop0% Iris.BI.BiEmbedLater.embed_later 5 := fun h =>
  (@h SiProp SiProp _ _ delayE iprop(False)).1 1 trivial
-- `Iris.BI.embed_mono` idx 7: necessary
theorem w5c0_88 : ¬ drop0% Iris.BI.embed_mono 7 := fun h =>
  (@h SiProp SiProp _ _ (idEmb _) iprop(True) iprop(False)) 0 trivial
-- `Iris.BI.embed_congr` idx 7: necessary
theorem w5c0_89 : ¬ drop0% Iris.BI.embed_congr 7 := fun h =>
  (@h SiProp SiProp _ _ (idEmb _) iprop(True) iprop(False)).1 0 trivial
-- `Iris.BI.embed_emp_valid_inj` idx 6: necessary
theorem w5c0_90 : ¬ drop0% Iris.BI.embed_emp_valid_inj 6 := fun h =>
  (@h SiProp SiProp _ _ (idEmb _) iprop(False)) 0 trivial
-- `Iris.BI.embed_sForall_elim` idx 7: necessary
theorem w5c0_91 : ¬ drop0% Iris.BI.embed_sForall_elim 7 := fun h =>
  (@h SiProp SiProp _ _ (idEmb _) (fun _ => False) iprop(False)) 0 (fun _ h => h.elim)
-- `Iris.BI.embed_sForall_intro` idx 7: necessary
theorem w5c0_92 : ¬ drop0% Iris.BI.embed_sForall_intro 7 := fun h =>
  (@h SiProp SiProp _ _ (idEmb _) (fun P => P = iprop(False)) iprop(True)) 0 trivial _ rfl
-- `Iris.BI.embed_sExists_intro` idx 7: necessary
theorem w5c0_93 : ¬ drop0% Iris.BI.embed_sExists_intro 7 := fun h => by
  obtain ⟨_, hf, _⟩ := (@h SiProp SiProp _ _ (idEmb _) (fun _ => False) iprop(True)) 0 trivial
  exact hf
-- `Iris.BI.embed_sExists_elim` idx 7: necessary
theorem w5c0_94 : ¬ drop0% Iris.BI.embed_sExists_elim 7 := fun h =>
  (@h SiProp SiProp _ _ (idEmb _) (fun P => P = iprop(True)) iprop(False)) 0 ⟨_, rfl, trivial⟩
-- `Iris.BI.embed_entails_inj` idx 7: necessary
theorem w5c0_95 : ¬ drop0% Iris.BI.embed_entails_inj 7 := fun h =>
  (@h SiProp SiProp _ _ (idEmb _) iprop(True) iprop(False)) 0 trivial
-- `Iris.BI.embed_inj` idx 7: necessary
theorem w5c0_96 : ¬ drop0% Iris.BI.embed_inj 7 := fun h => by
  have e := congrArg (fun P : SiProp => P.holds 0) (@h SiProp SiProp _ _ (idEmb _) iprop(True) iprop(False))
  exact cast e trivial
-- `Iris.BI.embed_emp` idx 5: necessary
theorem w5c0_97 : ¬ drop0% Iris.BI.embed_emp 5 := fun h =>
  na_true_not_emp ((spT (P := iprop(emp)) (fun _ _ => trivial)).trans (@h SiProp (UPred NA) _ _ (spE _)).1)
-- `Iris.BI.embed_affinely` idx 5: necessary
theorem w5c0_98 : ¬ drop0% Iris.BI.embed_affinely 5 := fun h =>
  na_true_not_emp ((spT (P := iprop(<affine> True)) (fun _ _ => ⟨trivial, trivial⟩)).trans
    ((@h SiProp (UPred NA) _ _ (spE _) iprop(True)).1.trans affinely_elim_emp))
-- `Iris.BI.embed_intuitionistically` idx 5: necessary
theorem w5c0_99 : ¬ drop0% Iris.BI.embed_intuitionistically 5 := fun h =>
  na_true_not_emp ((spT (P := iprop(□ True)) (fun _ _ => ⟨trivial, trivial⟩)).trans
    ((@h SiProp (UPred NA) _ _ (spE _) iprop(True)).1.trans intuitionistically_elim_emp))
-- `Iris.BI.embed_affinely_if` idx 5: necessary
theorem w5c0_100 : ¬ drop0% Iris.BI.embed_affinely_if 5 := fun h =>
  na_true_not_emp ((spT (P := iprop(<affine> True)) (fun _ _ => ⟨trivial, trivial⟩)).trans
    ((@h SiProp (UPred NA) _ _ (spE _) iprop(True) true).1.trans affinely_elim_emp))
-- `Iris.BI.embed_intuitionistically_if` idx 5: necessary
theorem w5c0_101 : ¬ drop0% Iris.BI.embed_intuitionistically_if 5 := fun h =>
  na_true_not_emp ((spT (P := iprop(□ True)) (fun _ _ => ⟨trivial, trivial⟩)).trans
    ((@h SiProp (UPred NA) _ _ (spE _) iprop(True) true).1.trans intuitionistically_elim_emp))
-- `Iris.BI.embed_persistent` idx 6: necessary
theorem w5c0_102 : ¬ drop0% Iris.BI.embed_persistent 6 := fun h =>
  own0_not_pers (fun _ h => h) (fun _ h => h) (@h HP HP _ _ (idEmb _) own0).persistent
-- `Iris.BI.embed_affine` idx 5: necessary
theorem w5c0_103 : ¬ drop0% Iris.BI.embed_affine 5 := fun h =>
  na_true_not_emp ((spT (P := iprop(emp)) (fun _ _ => trivial)).trans
    (@h SiProp (UPred NA) _ _ (spE _) iprop(emp) _).affine)
-- `Iris.BI.embed_affine` idx 7: necessary
theorem w5c0_104 : ¬ drop0% Iris.BI.embed_affine 7 := fun h =>
  na_true_not_emp (@h (UPred NA) (UPred NA) _ _ (idEmb _) (idEmp _) iprop(True)).affine
-- `Iris.BI.embed_absorbing` idx 6: necessary
theorem w5c0_105 : ¬ drop0% Iris.BI.embed_absorbing 6 := fun h =>
  heap_not_affine (sep_emp.2.trans (@h HP HP _ _ (idEmb _) iprop(emp)).absorbing)
-- `Iris.BI.embed_laterN` idx 5: necessary
theorem w5c0_106 : ¬ drop0% Iris.BI.embed_laterN 5 := fun h =>
  (@h SiProp SiProp _ _ delayE 1 iprop(False)).1 1 trivial
-- `Iris.BI.embed_except_0` idx 5: necessary
theorem w5c0_107 : ¬ drop0% Iris.BI.embed_except_0 5 := fun h =>
  ((@h SiProp SiProp _ _ delayE iprop(False)).1 1 (.inl trivial)).elim id id
-- `Iris.BI.embed_timeless` idx 7: necessary
theorem w5c0_109 : ¬ drop0% Iris.BI.embed_timeless 7 := fun h =>
  nt (@h SiProp SiProp _ _ (idEmb _) (idLat _) s0).timeless rfl Nat.one_ne_zero
-- `Iris.BI.embed_sep_homomorphism` idx 5: necessary
theorem w5c0_113 : ¬ drop0% Iris.BI.embed_sep_homomorphism 5 := fun h => by
  have e := (@h SiProp (UPred NA) _ _ (spE _)).map_unit
  have H := spT (PROP := UPred NA) (P := iprop(emp)) (fun _ _ => trivial)
  rw [e] at H
  exact na_true_not_emp H
-- `Iris.BI.embed_big_sepL` idx 5: necessary
theorem w5c0_114 : ¬ drop0% Iris.BI.embed_big_sepL 5 := fun h =>
  na_true_not_emp ((spTemp BigSepL.bigSepL_nil.2).trans
    ((@h SiProp (UPred NA) _ _ (spE _) Unit (fun _ _ => iprop(True)) []).1.trans BigSepL.bigSepL_nil.1))
-- `Iris.BI.embed_big_sepM` idx 9: necessary
theorem w5c0_115 : ¬ drop0% Iris.BI.embed_big_sepM 9 := fun h =>
  na_true_not_emp ((spTemp BigSepM.bigSepM_empty.2).trans
    ((@h SiProp (UPred NA) _ _ (spE _) Nat Unit (fun V => Std.ExtTreeMap Nat V compare) _
      (fun _ _ => iprop(True)) ∅).1.trans BigSepM.bigSepM_empty.1))
-- `Iris.BI.embed_big_sepS` idx 5: necessary
theorem w5c0_116 : ¬ drop0% Iris.BI.embed_big_sepS 5 := fun h =>
  na_true_not_emp ((spTemp BigSepS.bigSepS_empty.2).trans
    ((@h SiProp (UPred NA) _ _ (spE _) (Std.ExtTreeSet Nat compare) Nat _
      (fun _ => iprop(True)) ∅).1.trans BigSepS.bigSepS_empty.1))
-- `Iris.BI.embed_big_sepMS` idx 5: necessary
theorem w5c0_117 : ¬ drop0% Iris.BI.embed_big_sepMS 5 := fun h =>
  na_true_not_emp ((spTemp BigSepMS.bigSepMS_empty.2).trans
    ((@h SiProp (UPred NA) _ _ (spE _) (ListPerm Nat) Nat _
      (fun _ => iprop(True)) ∅).1.trans BigSepMS.bigSepMS_empty.1))

-- `Iris.BI.BiEmbedSbi.embed_siEmpValid` idx 7: necessary
theorem w5c0_86 : ¬ drop0% Iris.BI.BiEmbedSbi.embed_siEmpValid 7 := fun h =>
  Nat.one_ne_zero ((@h SiProp SiProp _ _ delayE _ _ s0).1 1 rfl)
-- `Iris.BI.BiEmbedSbi.embed_siPure_1` idx 7: necessary
theorem w5c0_87 : ¬ drop0% Iris.BI.BiEmbedSbi.embed_siPure_1 7 := fun h =>
  Nat.one_ne_zero ((@h SiProp SiProp _ _ delayE _ _ s0) 1 rfl)
-- `Iris.BI.embed_siPure` idx 5: necessary
theorem w5c0_118 : ¬ drop0% Iris.BI.embed_siPure 5 := fun h =>
  Nat.one_ne_zero ((@h SiProp SiProp _ _ delayE s0).1 1 rfl)
-- `Iris.BI.embed_internal_eq` idx 5: necessary
theorem w5c0_119 : ¬ drop0% Iris.BI.embed_internal_eq 5 := fun h => by
  have H : s0 ≡{1}≡ iprop(True) := (@h SiProp SiProp _ _ delayE SiProp _ s0 iprop(True)).1 1
    (show s0 ≡{0}≡ iprop(True) from fun {m} hm => ⟨fun _ => trivial, fun _ => by show m = 0; omega⟩)
  exact Nat.one_ne_zero ((H (m := 1) (Nat.le_refl 1)).2 trivial)
-- `Iris.BI.embed_plain` idx 5: necessary
theorem w5c0_120 : ¬ drop0% Iris.BI.embed_plain 5 := fun h => by
  have := (@h SiProp (MonPred I2 SiProp) _ _ eDE s0 ⟨fun _ h => h⟩).plain .hi 1 rfl
  exact absurd (this _ ⟨.lo, rfl⟩) (fun h' => Nat.one_ne_zero (h' : (1 : Nat) = 0))
-- `Iris.BI.embed_plain` idx 7: necessary
theorem w5c0_121 : ¬ drop0% Iris.BI.embed_plain 7 := fun h => by
  have := (@h (MonPred I2 SiProp) (MonPred I2 SiProp) _ _ (idEmb _) (idSbi _) (eD s0)).plain .hi 1 rfl
  exact absurd (this _ ⟨.lo, rfl⟩) (fun h' => Nat.one_ne_zero (h' : (1 : Nat) = 0))
-- `Iris.BI.embed_internal_inj` idx 5: necessary
theorem w5c0_122 : ¬ drop0% Iris.BI.embed_internal_inj 5 := fun h => by
  have H : s0 ≡{1}≡ iprop(True) := (@h SiProp SiProp _ _ delayE SiProp _ s0 iprop(True)) 1
    (show dl s0 ≡{1}≡ iprop(True) from fun {m} hm => ⟨fun _ => trivial, fun _ => by show m - 1 = 0; omega⟩)
  exact Nat.one_ne_zero ((H (m := 1) (Nat.le_refl 1)).2 trivial)
-- `Iris.BI.embed_embed_emp` idx 8: necessary
theorem w5c0_123 : ¬ drop0% Iris.BI.embed_embed_emp 8 := fun h =>
  na_true_not_emp ((spT (PROP := UPred NA) (P := iprop(emp)) (fun _ _ => trivial)).trans
    (@h SiProp (UPred NA) _ _ (UPred NA) _ (spE _) (idEmb _) (idEmp _)).embed_emp_1)
-- `Iris.BI.embed_embed_emp` idx 9: necessary
theorem w5c0_124 : ¬ drop0% Iris.BI.embed_embed_emp 9 := fun h =>
  na_true_not_emp ((spT (PROP := UPred NA) (P := iprop(emp)) (fun _ _ => trivial)).trans
    (@h SiProp (UPred NA) _ _ SiProp _ (idEmb _) (spE _) (idEmp _)).embed_emp_1)
-- `Iris.BI.embed_embed_later` idx 8: necessary
theorem w5c0_125 : ¬ drop0% Iris.BI.embed_embed_later 8 := fun h =>
  ((@h SiProp SiProp _ _ SiProp _ delayE (idEmb _) (idLat _)).embed_later iprop(False)).1 1 trivial
-- `Iris.BI.embed_embed_sbi` idx 8: necessary
theorem w5c0_130 : ¬ drop0% Iris.BI.embed_embed_sbi 8 := fun h =>
  Nat.one_ne_zero ((@h SiProp SiProp SiProp _ _ _ delayE (idEmb _) (idSbi _)).embed_siPure_1 s0 1 rfl)
-- `Iris.BI.embed_embed_sbi` idx 9: necessary
theorem w5c0_131 : ¬ drop0% Iris.BI.embed_embed_sbi 9 := fun h =>
  Nat.one_ne_zero ((@h SiProp SiProp SiProp _ _ _ (idEmb _) delayE (idSbi _)).embed_siPure_1 s0 1 rfl)
-- `Iris.BI.only0_absorbing` idx 3: necessary
theorem w5c0_35 : ¬ drop0% Iris.BI.only0_absorbing 3 := fun h => by
  have H : (iprop(True) : UPred NA) ⊢ iprop(<only0> emp) :=
    (sep_emp.2.trans (sep_mono_right only0_intro)).trans (@h (UPred NA) _ iprop(emp)).absorbing
  have H2 : (iprop(▷ False) : UPred NA) ⊢ emp := (and_intro true_intro .rfl).trans (imp_elim H)
  have H3 := H2 0 ⟨.a, trivial⟩ trivial
  cases H3

-- `Iris.BI.BiEmbedBUpd.embed_bupd` idx 7: necessary
theorem w5c0_84 : ¬ drop0% Iris.BI.BiEmbedBUpd.embed_bupd 7 := fun h =>
  (@h SiProp SiProp _ _ (idEmb _) idBupd exBupd iprop(False)).2 0 (Or.inl trivial)
-- `Iris.BI.embed_embed_bupd` idx 11: necessary
theorem w5c0_126 : ¬ drop0% Iris.BI.embed_embed_bupd 11 := fun h =>
  ((@h SiProp SiProp _ _ SiProp _ (idEmb _) (idEmb _) idBupd exBupd exBupd (idBU _)).embed_bupd
    iprop(False)).2 0 (Or.inl trivial)
-- `Iris.BI.embed_embed_bupd` idx 12: necessary
theorem w5c0_127 : ¬ drop0% Iris.BI.embed_embed_bupd 12 := fun h =>
  ((@h SiProp SiProp _ _ SiProp _ (idEmb _) (idEmb _) idBupd idBupd exBupd (idBU _)).embed_bupd
    iprop(False)).2 0 (Or.inl trivial)

-- helper: ownM 1 does not entail ownM 2 in UPred Credit (copied from Probe2)
open ORA in
theorem cm_bad (h : (UPred.ownM (1 : Credit)) ⊢ UPred.ownM (2 : Credit)) : False := by
  have := h 0 ⟨1, (OFE.Dist.validN rfl).mp trivial⟩ (ordN_refl _)
  simp [UPred.ownM] at this
  obtain ⟨z, hz⟩ := this
  have hz' : (1 : Nat) = 2 + z := hz
  omega

-- `Iris.BI.mkEmbedHom` idx 11: necessary
theorem w5c0_112 : ¬ drop0% Iris.BI.mkEmbedHom 11 := fun h => by
  have e := (@h (UPred Credit) (UPred Credit) _ _ (idEmb _) BIBase.and BIBase.sep iprop(True) iprop(emp)
    andMonoidOps sepMonoidOps true_emp.to_eq).map_op (x := UPred.ownM (1 : Credit)) (y := UPred.ownM (1 : Credit))
  have H : (UPred.ownM (1 : Credit)) ⊢ iprop(UPred.ownM (1 : Credit) ∗ UPred.ownM (1 : Credit)) := by
    have H0 : (UPred.ownM (1 : Credit)) ⊢ iprop(UPred.ownM (1 : Credit) ∧ UPred.ownM (1 : Credit)) :=
      and_intro .rfl .rfl
    exact e ▸ H0
  exact cm_bad (H.trans (UPred.ownM_op (1 : Credit) 1).2)

-- helper: SiProp extensionality (as in Probe2)
theorem sp_ext {P Q : SiProp} (h : ∀ n, P.holds n ↔ Q.holds n) : P = Q := by
  obtain ⟨p, _⟩ := P; obtain ⟨q, _⟩ := Q
  have : p = q := funext fun n => propext (h n)
  subst this; rfl
-- helper: conjunction guarded by "holds at 0 implies holds at 1" on the left argument; agrees with
-- conjunction on the image of the delay embedding but is not commutative
def op3 (x y : SiProp) : SiProp :=
  ⟨fun n => x.holds n ∧ y.holds n ∧ (x.holds 0 → x.holds 1),
   fun h hle => ⟨x.closed h.1 hle, y.closed h.2.1 hle, h.2.2⟩⟩

-- `Iris.BI.mkEmbedHom` idx 10: necessary
theorem w5c0_111 : ¬ indep0% Iris.BI.mkEmbedHom 10 := fun h => by
  have H := @h SiProp SiProp _ _ delayE BIBase.and op3 iprop(True) iprop(True) andMonoidOps
    (fun {x y} => sp_ext fun n => ⟨fun h => ⟨h.1, h.2, fun h0 => h0⟩, fun h => ⟨h.1, h.2.1⟩⟩)
    (sp_ext fun n => Iff.rfl)
  have c := congrArg (fun P : SiProp => P.holds 0) (H.op_comm (a := s0) (b := iprop(True)))
  have c' : (s0.holds 0 ∧ True ∧ (s0.holds 0 → s0.holds 1)) = (True ∧ s0.holds 0 ∧ (True → True)) := c
  have : s0.holds 0 ∧ True ∧ (s0.holds 0 → s0.holds 1) := c' ▸ ⟨trivial, rfl, fun _ => trivial⟩
  exact Nat.one_ne_zero (this.2.2 rfl)


-- helper: TP (copied from W4c1): non-affine step-indexed BI on Bool resources, emp = (n = 0 or m = false), not timeless
structure TP where
  holds : Nat → Bool → Prop
  mono {n n' : Nat} {m : Bool} : holds n m → n' ≤ n → holds n' m
  irr {m m' : Bool} : holds 0 m → holds 0 m'

theorem TP.ext' : {P Q : TP} → (∀ n m, P.holds n m ↔ Q.holds n m) → P = Q
  | ⟨p, _, _⟩, ⟨q, _, _⟩, h => by
    have : p = q := funext fun n => funext fun m => propext (h n m)
    subst this; rfl

def TP.emp : TP where
  holds n m := n = 0 ∨ m = false
  mono h hle := by rcases h with h | h; exact .inl (by omega); exact .inr h
  irr _ := .inl rfl
def TP.pure (φ : Prop) : TP where
  holds _ _ := φ
  mono h _ := h
  irr h := h
def TP.and (P Q : TP) : TP where
  holds n m := P.holds n m ∧ Q.holds n m
  mono h hle := ⟨P.mono h.1 hle, Q.mono h.2 hle⟩
  irr h := ⟨P.irr h.1, Q.irr h.2⟩
def TP.or (P Q : TP) : TP where
  holds n m := P.holds n m ∨ Q.holds n m
  mono h hle := h.elim (fun h => .inl (P.mono h hle)) (fun h => .inr (Q.mono h hle))
  irr h := h.elim (fun h => .inl (P.irr h)) (fun h => .inr (Q.irr h))
def TP.imp (P Q : TP) : TP where
  holds n m := ∀ n', n' ≤ n → P.holds n' m → Q.holds n' m
  mono h hle n'' h'' hp := h n'' (Nat.le_trans h'' hle) hp
  irr h n' hn' hp := by
    obtain rfl : n' = 0 := by omega
    exact Q.irr (h 0 (Nat.le_refl 0) (P.irr hp))
def TP.sForall (Ψ : TP → Prop) : TP where
  holds n m := ∀ p, Ψ p → p.holds n m
  mono h hle p hp := p.mono (h p hp) hle
  irr h p hp := p.irr (h p hp)
def TP.sExists (Ψ : TP → Prop) : TP where
  holds n m := ∃ p, Ψ p ∧ p.holds n m
  mono h hle := let ⟨p, hp, h⟩ := h; ⟨p, hp, p.mono h hle⟩
  irr h := let ⟨p, hp, h⟩ := h; ⟨p, hp, p.irr h⟩
def TP.sep (P Q : TP) : TP where
  holds n m := ∃ a b, m = Bool.or a b ∧ P.holds n a ∧ Q.holds n b
  mono h hle := let ⟨a, b, e, hp, hq⟩ := h; ⟨a, b, e, P.mono hp hle, Q.mono hq hle⟩
  irr {_ m'} h := let ⟨_, _, _, hp, hq⟩ := h; ⟨m', false, by cases m' <;> rfl, P.irr hp, Q.irr hq⟩
def TP.wand (P Q : TP) : TP where
  holds n m := ∀ n', n' ≤ n → ∀ b, P.holds n' b → Q.holds n' (Bool.or m b)
  mono h hle n'' h'' b hp := h n'' (Nat.le_trans h'' hle) b hp
  irr h n' hn' b hp := by
    obtain rfl : n' = 0 := by omega
    exact Q.irr (h 0 (Nat.le_refl 0) b hp)
def TP.pers (P : TP) : TP where
  holds n _ := P.holds n false
  mono h hle := P.mono h hle
  irr h := h
def TP.later (P : TP) : TP where
  holds n m := match n with | 0 => True | k+1 => P.holds k m
  mono {n n' m} h hle := by
    cases n' with
    | zero => trivial
    | succ k' => cases n with
      | zero => omega
      | succ k => exact P.mono h (by omega)
  irr _ := trivial

instance : BIBase TP where
  Entails P Q := ∀ n m, P.holds n m → Q.holds n m
  emp := TP.emp
  pure := TP.pure
  and := TP.and
  or := TP.or
  imp := TP.imp
  sForall := TP.sForall
  sExists := TP.sExists
  sep := TP.sep
  wand := TP.wand
  persistently := TP.pers
  later := TP.later

instance : COFE TP := COFE.ofDiscrete _

instance tpBI : BI TP where
  entails_refl _ _ h := h
  entails_trans h1 h2 n m h := h2 n m (h1 n m h)
  equiv_iff {P Q} := ⟨fun h => h ▸ ⟨fun _ _ h => h, fun _ _ h => h⟩,
    fun ⟨h1, h2⟩ => TP.ext' fun n m => ⟨h1 n m, h2 n m⟩⟩
  and_ne := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  or_ne := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  imp_ne := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  sep_ne := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  wand_ne := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  persistently_ne := ⟨by rintro _ _ _ h; exact (h : _ = _) ▸ rfl⟩
  later_ne := ⟨by rintro _ _ _ h; exact (h : _ = _) ▸ rfl⟩
  sForall_ne {_ P Q} h := (liftRel_eq.1 (h : liftRel Eq P Q)) ▸ rfl
  sExists_ne {_ P Q} h := (liftRel_eq.1 (h : liftRel Eq P Q)) ▸ rfl
  pure_intro h _ _ _ := h
  pure_elim' h n m hφ := h hφ n m trivial
  and_elim_l _ _ h := h.1
  and_elim_r _ _ h := h.2
  and_intro h1 h2 n m h := ⟨h1 n m h, h2 n m h⟩
  or_intro_l _ _ h := .inl h
  or_intro_r _ _ h := .inr h
  or_elim h1 h2 n m h := h.elim (h1 n m) (h2 n m)
  imp_intro {P _ _} h n m hp n' hle hq := h n' m ⟨P.mono hp hle, hq⟩
  imp_elim h n m hpq := h n m hpq.1 n (Nat.le_refl n) hpq.2
  sForall_intro h n m hp p hΨ := h p hΨ n m hp
  sForall_elim hΨ n m h := h _ hΨ
  sExists_intro hΨ n m h := ⟨_, hΨ, h⟩
  sExists_elim h n m := fun ⟨p, hp, hh⟩ => h p hp n m hh
  sep_mono h1 h2 n m := fun ⟨a, b, e, hp, hq⟩ => ⟨a, b, e, h1 n a hp, h2 n b hq⟩
  emp_sep {P} := ⟨fun n m ⟨a, b, e, he, hp⟩ => by
      rcases he with he | he
      · subst he; exact P.irr hp
      · subst he; cases b <;> (subst e; exact hp),
    fun n m hp => ⟨false, m, by cases m <;> rfl, .inr rfl, hp⟩⟩
  sep_symm n m := fun ⟨a, b, e, hp, hq⟩ => ⟨b, a, by rw [e, Bool.or_comm], hq, hp⟩
  sep_assoc_l n m := fun ⟨_, c, e, ⟨a, b, e', hp, hq⟩, hr⟩ =>
    ⟨a, or b c, by rw [e, e', Bool.or_assoc], hp, b, c, rfl, hq, hr⟩
  wand_intro {P _ _} h n m hp n' hle b hq := h n' (Bool.or m b) ⟨m, b, rfl, P.mono hp hle, hq⟩
  wand_elim h n m := fun ⟨a, b, e, hp, hq⟩ => e ▸ h n a hp n (Nat.le_refl n) b hq
  persistently_mono h n _ hp := h n false hp
  persistently_idem_2 _ _ h := h
  persistently_emp_2 _ _ _ := .inr rfl
  persistently_and_2 _ _ h := h
  persistently_absorb_l n m := fun ⟨_, _, _, hp, _⟩ => hp
  persistently_and_l n m := fun ⟨hp, hq⟩ => ⟨false, m, by cases m <;> rfl, hp, hq⟩
  later_mono h n m hp := by
    cases n with
    | zero => trivial
    | succ k => exact h k m hp
  later_intro {P} n m hp := by
    cases n with
    | zero => trivial
    | succ k => exact P.mono hp (Nat.le_succ k)
  later_sForall_2 n m h := by
    cases n with
    | zero => trivial
    | succ k => exact fun p hp => h _ ⟨p, rfl⟩ (k+1) (Nat.le_refl _) hp
  later_sExists_false n m h := by
    cases n with
    | zero => exact .inl trivial
    | succ k =>
      obtain ⟨p, hp, hh⟩ := h
      exact .inr ⟨_, ⟨p, rfl⟩, hp, hh⟩
  later_sep := ⟨fun n m h => by
      cases n with
      | zero => exact ⟨m, false, by cases m <;> rfl, trivial, trivial⟩
      | succ k => exact h,
    fun n m h => by
      cases n with
      | zero => trivial
      | succ k => exact h⟩
  later_persistently := ⟨fun n m h => by cases n <;> exact h, fun n m h => by cases n <;> exact h⟩
  later_false_em {P} n m h := by
    cases n with
    | zero => exact .inl trivial
    | succ k =>
      refine .inr fun n' hle hf => ?_
      cases n' with
      | zero => exact P.mono h (Nat.zero_le _)
      | succ j => exact hf.elim

theorem tp_emp_not_timeless : ¬ Timeless (emp : TP) := fun ⟨h⟩ => by
  have := h 1 true (.inl rfl)
  rcases this with h1 | h1
  · exact h1
  · rcases h1 with h1 | h1 <;> simp at h1

-- helper: TP has Loeb (induction on the step index)
instance tpLoeb : BILoeb TP := ⟨fun {P} h => by
  intro n m _
  induction n generalizing m with
  | zero => exact h 0 m trivial
  | succ k ih => exact h (k+1) m (ih m trivial)⟩
-- helper: TP satisfies BIPersistentlyExist (persistently reads the resource false, exists is pointwise)
instance tpPE : BIPersistentlyExist TP :=
  ⟨fun Ψ n m ⟨p, hΨ, hp⟩ => ⟨_, ⟨p, rfl⟩, hΨ, hp⟩⟩
-- helper: a TP prop holding at (0, true) but not at (1, true) is not timeless
theorem tpbad {Q : TP} (h : iprop(▷ Q) ⊢ iprop(◇ Q)) (h0 : Q.holds 0 true) (h1 : ¬ Q.holds 1 true) :
    False := by
  rcases h 1 true h0 with h' | h'
  · exact h'
  · exact h1 h'
theorem tpTrue : Timeless (iprop(True) : TP) := ⟨(pure_intro trivial).trans except0_intro⟩

-- `Iris.BI.emp_timeless` idx 2: necessary
theorem w5c0_42 : ¬ drop0% Iris.BI.emp_timeless 2 := fun h =>
  tp_emp_not_timeless (@h TP _)
-- `Iris.BI.affinely_timeless` idx 2: necessary
theorem w5c0_58 : ¬ drop0% Iris.BI.affinely_timeless 2 := fun h =>
  tpbad (@h TP _ iprop(True) tpTrue).timeless ⟨.inl rfl, trivial⟩
    (fun h1 => by rcases h1.1 with h | h <;> simp at h)
-- `Iris.BI.intuitionistically_timeless` idx 3: necessary
theorem w5c0_62 : ¬ drop0% Iris.BI.intuitionistically_timeless 3 := fun h =>
  tpbad (@h TP _ _ iprop(True) tpTrue).timeless ⟨.inl rfl, trivial⟩
    (fun h1 => by rcases h1.1 with h | h <;> simp at h)
-- `Iris.BI.later_affinely_mp` idx 3: necessary
theorem w5c0_29 : ¬ drop0% Iris.BI.later_affinely_mp 3 := fun h => by
  rcases (@h TP _ iprop(True)) 1 true ⟨.inl rfl, trivial⟩ with h' | h'
  · exact h'
  · rcases h'.1 with h | h <;> simp at h
-- `Iris.BI.only0_emp` idx 3: necessary
theorem w5c0_71 : ¬ drop0% Iris.BI.only0_emp 3 := fun h => by
  have H := (@h TP _ _).1 1 true (fun n' _ hf => by
    cases n' with
    | zero => exact .inl rfl
    | succ k => exact absurd hf id)
  rcases H with h | h <;> simp at h
-- `Iris.BI.only0_affinely` idx 3: necessary
theorem w5c0_75 : ¬ drop0% Iris.BI.only0_affinely 3 := fun h => by
  have H := (@h TP _ _ iprop(True)).1 1 true (fun n' _ hf => by
    cases n' with
    | zero => exact ⟨.inl rfl, trivial⟩
    | succ k => exact absurd hf id)
  rcases H.1 with h | h <;> simp at h
end W5c0
