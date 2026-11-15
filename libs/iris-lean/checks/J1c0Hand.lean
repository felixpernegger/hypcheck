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

/-! ## Joint removal of two hypotheses (J1c0)

`drop2% T i j` / `drop2_0% T i j`: `T` with its two non-dependent Prop binders `i < j` dropped
(`_0`: universes set to `0`, for refutations only).
`indep2% T i j` / `indep2_0% T i j`: for two dependent Prop binders (the conclusion or later
binders mention them): `∀ rest, Hᵢ ∧ Hⱼ`, where `rest` are the binders that depend on neither;
"jointly removable" means both are derivable from `rest`. -/

def hcDrop2 (T : Ident) (i j : Nat) (zero : Bool) : TermElabM Lean.Expr := do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us ← if zero then pure (ci.levelParams.map fun _ => Level.zero)
    else ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    unless i < j && j < xs.size do throwError "need i < j < {xs.size}"
    for k in [i, j] do
      let x := xs[k]!
      unless ← isProp (← inferType x) do throwError "binder {k} of {n} is not a Prop"
      for l in [k+1:xs.size] do
        if (← inferType xs[l]!).containsFVar x.fvarId! then throwError "binder {k} of {n} is dependent"
      if body.containsFVar x.fvarId! then throwError "binder {k} of {n} is dependent"
    mkForallFVars (xs.filter fun y => y != xs[i]! && y != xs[j]!) body

def hcIndep2 (T : Ident) (i j : Nat) (zero : Bool) : TermElabM Lean.Expr := do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us ← if zero then pure (ci.levelParams.map fun _ => Level.zero)
    else ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    unless i < j && j < xs.size do throwError "need i < j < {xs.size}"
    let xi := xs[i]!; let xj := xs[j]!
    for x in [xi, xj] do
      unless ← isProp (← inferType x) do throwError "binder of {n} is not a Prop"
    let hi ← inferType xi; let hj ← inferType xj
    if hj.containsFVar xi.fvarId! then throwError "Hⱼ mentions binder {i}"
    let mut dep := #[xi, xj]
    for l in [i+1:xs.size] do
      if l == j then continue
      let t ← inferType xs[l]!
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push xs[l]!
    unless or (dep.size > 2) (or (body.containsFVar xi.fvarId!) (body.containsFVar xj.fvarId!)) do
      throwError "neither binder is dependent: use drop2%"
    mkForallFVars (xs.filter (!dep.contains ·)) (mkAnd hi hj)

elab "drop2% " T:ident i:num j:num : term => hcDrop2 T i.getNat j.getNat false
elab "drop2_0% " T:ident i:num j:num : term => hcDrop2 T i.getNat j.getNat true
elab "indep2% " T:ident i:num j:num : term => hcIndep2 T i.getNat j.getNat false
elab "indep2_0% " T:ident i:num j:num : term => hcIndep2 T i.getNat j.getNat true

/-! ## Helpers (copied from the hand files that proved the single removals) -/


namespace J1c0
open Iris Iris.BI Iris.OFE Iris.Algebra Iris.Std

/-- Truncation OFE on naturals (copy of Probe1 TN): 1 and 2 agree at step 0. -/
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

/-- Non-non-expansive map on TN: 1 ↦ 0, else ↦ 1 (copy of W1c0). -/
def bad (x : TN) : TN := if x.v = 1 then ⟨0⟩ else ⟨1⟩
/-- Agreement element with the given TN values (copy of W1c0). -/
def RA (l : List Nat) (h : l ≠ [] := by simp) : Agree.Raw TN := ⟨l.map TN.mk, by simpa using h⟩
def AA (l : List Nat) (h : l ≠ [] := by simp) : Agree TN := Agree.mk (RA l h)

/-- Discrete OFE on Nat and (Nat, +, 0) (copy of W1c1). -/
instance natOFE : OFE Nat := OFE.ofDiscrete Nat
theorem natNE2 (f : Nat → Nat → Nat) : OFE.NonExpansive₂ f :=
  ⟨fun n x₁ x₂ h y₁ y₂ h' => by
    change x₁ = x₂ at h; change y₁ = y₂ at h'; subst h h'; exact OFE.Dist.of_eq rfl⟩
def ad (a b : Nat) : Nat := a + b
instance addMon : MonoidOps ad 0 where
  op_ne := natNE2 _
  op_assoc := Nat.add_assoc _ _ _
  op_comm := Nat.add_comm _ _
  op_left_id := Nat.zero_add _
abbrev TM (V : Type) := Std.ExtTreeMap Nat V compare
open LawfulPartialMap in
theorem emptyGet {V : Type} {k : Nat} {y : V} (e : get? (∅ : TM V) k = some y) : False := by
  rw [get?_empty] at e; cases e

/-- Natural-number BI index (copy of W5c5 UIdx). -/
abbrev UIdx : BiIndex := { car := Nat, rel := inferInstance }

/-- Discrete COFE on Bool (copy of W3c1 DB). -/
structure DB where v : Bool
deriving DecidableEq
instance dbCOFE : COFE DB := COFE.ofDiscrete DB
instance dbDisc : OFE.Discrete DB := ⟨id⟩
instance : Inhabited DB := ⟨⟨false⟩⟩
def notDB (x : DB) : DB := ⟨!x.v⟩
theorem notDB_inv (x : DB) : notDB (notDB x) = x := by cases x; simp [notDB]
def homNot : DB -n> DB := ⟨notDB, ⟨fun {n x y} h => (OFE.Discrete.discrete_0 (h.le (Nat.zero_le n)) : x = y) ▸ Dist.rfl⟩⟩
def isoId : Iso DB DB := ⟨Hom.id, Hom.id, rfl, rfl⟩
def isoNot : Iso DB DB := ⟨homNot, homNot, notDB_inv _, notDB_inv _⟩

/-- Cantor space (copy of W3c1 CS): non-discrete COFE of Bool streams. -/
structure CS where s : Nat → Bool
instance csOFE : OFE CS where
  Dist n x y := ∀ k, k ≤ n → x.s k = y.s k
  dist_eqv := ⟨fun _ _ _ => rfl, fun h k hk => (h k hk).symm, fun h1 h2 k hk => (h1 k hk).trans (h2 k hk)⟩
  eq_dist' {x y} := ⟨fun h n k _ => h ▸ rfl, fun h => by
      cases x with | mk a => cases y with | mk b =>
      congr; funext k; exact h k k (Nat.le_refl k)⟩
  dist_lt {n x y m} h hm k hk := h k (by omega)
instance csCOFE : IsCOFE CS where
  compl c := ⟨fun k => (c.chain k).s k⟩
  conv_compl {n c} k hk := ((c.cauchy hk) k (Nat.le_refl k)).symm
instance : Inhabited CS := ⟨⟨fun _ => false⟩⟩
def cF : CS := ⟨fun _ => false⟩
def cT : CS := ⟨fun _ => true⟩
theorem cTF0 : ¬ cT ≡{0}≡ cF := fun h => nomatch h 0 (Nat.le_refl 0)
theorem id_not_contr : ¬ Contractive (fun x : CS => x) := fun h =>
  cTF0 (h.distLater_dist (n := 0) (x := cT) (y := cF) distLater_zero)
/-- Stream true only at index 1. -/
def e1 : CS := ⟨fun k => decide (k = 1)⟩
/-- Map whose second iterate is constant, but which is not non-expansive (index 0 copies index 1). -/
def kf (w : CS) : CS := ⟨fun k => if k = 0 then w.s 1 else if k = 1 then true else false⟩
instance kfC : Contractive (Nat.repeat kf 2) := ⟨fun _ _ _ => rfl⟩
theorem kf_not_ne : ¬ NonExpansive kf := fun h => by
  have := h.ne (n := 0) (x₁ := cF) (x₂ := e1) (fun k hk => by
    have : k = 0 := by omega
    subst this; rfl) 0 (Nat.le_refl 0)
  simp [kf, cF, e1] at this

/-- zip and set commute (copy of W4c1). -/
theorem zipSet {C D : Type _} : ∀ (l1 : List C) (l2 : List D) (i : Nat) (y1 : C) (y2 : D),
    (l1.zip l2).set i (y1, y2) = (l1.set i y1).zip (l2.set i y2)
  | [], _, _, _, _ => by simp
  | _::_, [], _, _, _ => by simp
  | _::_, _::_, 0, _, _ => by simp
  | _::xs, _::ys, i+1, y1, y2 => by simp [zipSet xs ys i y1 y2]

/-- laterN_False without BIPersistentlyExist (copy of W5c2). -/
theorem laterNFalse_gen.{u} {PROP : Type u} [BI PROP] [BILoeb PROP] : ⊢@{PROP} ∃ n, ▷^[n] False := by
  refine true_intro.trans (loeb_weak ?_)
  exact later_exists_false.trans (or_elim (exists_intro (Ψ := fun n => iprop(▷^[n] False)) 1)
    (exists_elim fun n => exists_intro (Ψ := fun n => iprop(▷^[n] False)) (n + 1)))

end J1c0

namespace J1c0
open Iris Iris.BI

section SavedGen
universe u v
variable {PROP : Type u} [BI PROP] (ident : Type v) (saved : ident → PROP → PROP)
  (agree : ∀ (i : ident) (P Q : PROP), saved i P ∧ saved i Q ⊢ □ (P ↔ Q))
include agree

/-- The core of saved_NA from separated facts: if □(¬P ∗ saved i P) yields ¬P and saved i P,
then saved i (A i) ∧ A i is contradictory (only ∧-reasoning and agree). -/
theorem savedNA_core (i : ident)
    (hl : ∀ P : PROP, iprop(□ (¬P ∗ saved i P)) ⊢ iprop(¬P))
    (hr : ∀ P : PROP, iprop(□ (¬P ∗ saved i P)) ⊢ saved i P) :
    saved i (Iris.SavedProp.A ident saved i) ⊢ iprop(¬ Iris.SavedProp.A ident saved i) := by
  refine imp_intro ?_
  refine (and_intro .rfl and_elim_r).trans (and_exists_left.mp.trans (exists_elim fun P => ?_))
  let X : PROP := iprop((saved i (Iris.SavedProp.A ident saved i) ∧ Iris.SavedProp.A ident saved i) ∧
      □ (¬P ∗ saved i P))
  have h1 : X ⊢ iprop(¬P) := and_elim_r.trans (hl P)
  have h2 : X ⊢ saved i P := and_elim_r.trans (hr P)
  have h3 : X ⊢ saved i (Iris.SavedProp.A ident saved i) := and_elim_l.trans and_elim_l
  have h4 : X ⊢ Iris.SavedProp.A ident saved i := and_elim_l.trans and_elim_r
  have h5 := (and_intro h2 h3).trans (agree i P (Iris.SavedProp.A ident saved i))
  have h6 := (and_intro (h5.trans (intuitionistically_elim.trans and_elim_r)) h4).trans imp_elim_left
  exact (and_intro h1 h6).trans imp_elim_left

/-- agree makes every saved i P affine. -/
theorem saved_affine (i : ident) (P : PROP) : Affine (saved i P) :=
  ⟨(and_intro .rfl .rfl).trans ((agree i P P).trans intuitionistically_elim_emp)⟩

/-- saved_NA with persistence of saved (no BIAffine, no BIPersistentlyExist). -/
theorem savedNA_pers [∀ i P, Persistent (saved i P)] (i : ident) :
    saved i (Iris.SavedProp.A ident saved i) ⊢ iprop(¬ Iris.SavedProp.A ident saved i) := by
  refine savedNA_core ident saved agree i (fun P => ?_) (fun P => ?_)
  · haveI := saved_affine ident saved agree i P
    exact intuitionistically_elim.trans sep_elim_left
  · exact (intuitionistically_mono ((sep_mono_right persistent).trans persistently_absorb_right)).trans
      ((affinely_mono persistently_idem.1).trans intuitionistically_elim)

/-- saved_NA in an affine BI (no persistence of saved, no BIPersistentlyExist). -/
theorem savedNA_aff [BIAffine PROP] (i : ident) :
    saved i (Iris.SavedProp.A ident saved i) ⊢ iprop(¬ Iris.SavedProp.A ident saved i) :=
  savedNA_core ident saved agree i (fun _ => intuitionistically_elim.trans sep_elim_left)
    (fun _ => intuitionistically_elim.trans sep_elim_right)

/-- saved_A with persistence of saved (no BIAffine, no BIPersistentlyExist). -/
theorem savedA_pers [∀ i P, Persistent (saved i P)] (i : ident) :
    saved i (Iris.SavedProp.A ident saved i) ⊢ Iris.SavedProp.A ident saved i := by
  haveI := saved_affine ident saved agree i (Iris.SavedProp.A ident saved i)
  refine intuitionistic_alias.trans (Iris.BI.BIBase.Entails.trans ?_
    (exists_intro (Ψ := fun P => iprop(□ (¬P ∗ saved i P))) (Iris.SavedProp.A ident saved i)))
  exact intuitionistically_intro_intuitionistically (intuitionistically_sep_idem.2.trans
    (sep_mono (intuitionistically_elim.trans (savedNA_pers ident saved agree i)) intuitionistically_elim))

end SavedGen

/-- SavedProp.contradiction from alloc, agree, consistency and persistence of saved only. -/
theorem sp_contra {PROP : Type _} [BI PROP] (bupd : PROP → PROP) (ident : Type _) (saved : ident → PROP → PROP)
    [∀ i P, Persistent (saved i P)]
    (alloc : ∀ {P : ident → PROP}, ⊢ bupd iprop(∃ i, saved i (P i)))
    (agree : ∀ (i : ident) (P Q : PROP), saved i P ∧ saved i Q ⊢ □ (P ↔ Q))
    (cons : ¬(⊢ bupd iprop(False))) : False := by
  apply cons
  have hF : iprop(∃ i, saved i (Iris.SavedProp.A ident saved i)) ⊣⊢ iprop(False) :=
    ⟨exists_elim fun i => (and_intro (savedNA_pers ident saved agree i)
      (savedA_pers ident saved agree i)).trans imp_elim_left, false_elim⟩
  rw [← Iris.BI.BIBase.BiEntails.to_eq hF]
  exact alloc

/-- Inv.saved_alloc from sts_alloc, mask_mono, inv_alloc, mono and fupd_fupd only. -/
theorem sa_core {PROP : Type _} [BI PROP] (fupd : Iris.Inv.Mask → PROP → PROP) (name : Type _)
    (inv : name → PROP → PROP)
    (hm : ∀ {E : Iris.Inv.Mask} {P Q : PROP}, (P ⊢ Q) → fupd E P ⊢ fupd E Q)
    (hff : ∀ {E : Iris.Inv.Mask} {P : PROP}, fupd E (fupd E P) ⊢ fupd E P)
    (hmm : ∀ {P : PROP}, fupd Iris.Inv.Mask.M0 P ⊢ fupd Iris.Inv.Mask.M1 P)
    (hia : ∀ (P : PROP), P ⊢ fupd Iris.Inv.Mask.M1 iprop(∃ i, inv i P))
    (gname : Type _) (start finished : gname → PROP)
    (sts : ⊢ fupd Iris.Inv.Mask.M0 iprop(∃ γ, start γ)) (P : gname → PROP) :
    ⊢ fupd Iris.Inv.Mask.M1 iprop(∃ γ, Iris.Inv.saved name inv gname start finished γ (P γ)) :=
  (sts.trans hmm).trans ((hm (exists_elim fun γ => or_intro_l.trans ((hia _).trans
    (hm (exists_intro (Ψ := fun γ => Iris.Inv.saved name inv gname start finished γ (P γ)) γ))))).trans hff)
end J1c0

namespace J1c0
open Iris Iris.BI

section SavedNoAff
universe u v
variable {PROP : Type u} [BI PROP] (ident : Type v) (saved : ident → PROP → PROP)
  (agree : ∀ (i : ident) (P Q : PROP), saved i P ∧ saved i Q ⊢ □ (P ↔ Q))
include agree

/-- saved_NA with neither BIAffine nor persistence of saved: agree makes every saved i P affine;
□(¬P ∗ saved i P) gives <pers> ¬P, <pers> A i, and with saved i (A i) also <pers> (P ↔ A i)
(the stray ¬P is absorbed by <pers>); all three meet under <pers>, giving <pers> False. -/
theorem savedNA_gen (i : ident) :
    saved i (Iris.SavedProp.A ident saved i) ⊢ iprop(¬ Iris.SavedProp.A ident saved i) := by
  haveI hAff : ∀ P, Affine (saved i P) := fun P => saved_affine ident saved agree i P
  refine imp_intro ?_
  refine and_exists_left.mp.trans (exists_elim fun P => ?_)
  have hY : iprop(□ (¬P ∗ saved i P)) ⊢ Iris.SavedProp.A ident saved i :=
    exists_intro (Ψ := fun P => iprop(□ (¬P ∗ saved i P))) P
  have hN : iprop(□ (¬P ∗ saved i P)) ⊢ iprop(<pers> (¬P)) :=
    (intuitionistically_mono sep_elim_left).trans persistently_of_intuitionistically
  have hA : iprop(□ (¬P ∗ saved i P)) ⊢ iprop(<pers> Iris.SavedProp.A ident saved i) :=
    persistently_intro.trans (persistently_mono hY)
  have hQ : iprop(□ (¬P ∗ saved i P) ∗ saved i (Iris.SavedProp.A ident saved i)) ⊢
      iprop(<pers> (P ↔ Iris.SavedProp.A ident saved i)) :=
    (sep_mono_left intuitionistically_elim).trans <| sep_assoc.1.trans <|
      (sep_mono_right ((and_intro sep_elim_left sep_elim_right).trans
        ((agree i P (Iris.SavedProp.A ident saved i)).trans persistently_of_intuitionistically))).trans
        persistently_absorb_right
  have hall : iprop(saved i (Iris.SavedProp.A ident saved i) ∧ □ (¬P ∗ saved i P)) ⊢
      iprop(<pers> (¬P) ∗ (<pers> Iris.SavedProp.A ident saved i ∗
        <pers> (P ↔ Iris.SavedProp.A ident saved i))) :=
    persistent_and_sep_mp.trans <| sep_comm.1.trans <|
      (sep_mono_left (intuitionistically_sep_idem.2.trans (sep_mono_right intuitionistically_sep_idem.2))).trans <|
      sep_assoc.1.trans <| sep_mono hN (sep_assoc.1.trans (sep_mono hA hQ))
  have hP : iprop(Iris.SavedProp.A ident saved i ∧ (P ↔ Iris.SavedProp.A ident saved i)) ⊢ P :=
    (and_intro (and_elim_r.trans and_elim_r) and_elim_l).trans imp_elim_left
  have hF : iprop(¬P ∧ (Iris.SavedProp.A ident saved i ∧ (P ↔ Iris.SavedProp.A ident saved i))) ⊢ iprop(False) :=
    (and_intro and_elim_l (and_elim_r.trans hP)).trans imp_elim_left
  exact hall.trans <| ((sep_mono_right sep_and).trans sep_and).trans <|
    ((and_mono_right persistently_and.2).trans persistently_and.2).trans <|
    (persistently_mono hF).trans (persistently_pure.1.trans false_elim)
end SavedNoAff
end J1c0


namespace J1c0
open Iris Iris.BI Iris.OFE

section gen
variable {PROP : Type _} [Sbi PROP] {A : Type _} [OFE A] (R : A → A → PROP)

theorem rtc_intro (x₁ x₂ : A) : biRtcPre R x₂ (fun x => biRtc R x x₂) x₁ ⊢ biRtc R x₁ x₂ := by
  unfold biRtcPre biRtc
  iintro H %Φ #Hc
  iapply Hc
  iunfold biRtcPre
  icases H with ⟨H | ⟨%x', HR, Hr⟩⟩
  · ileft; iexact H
  · iright; iexists x'; iframe HR
    ispecialize Hr $$ %Φ
    iapply Hr; iexact Hc

theorem tc_intro (x₁ x₂ : A) : biTcPre R x₂ (fun x => biTc R x x₂) x₁ ⊢ biTc R x₁ x₂ := by
  unfold biTcPre biTc
  iintro H %Φ #Hc
  iapply Hc
  iunfold biTcPre
  icases H with ⟨H | ⟨%x', HR, Hr⟩⟩
  · ileft; iexact H
  · iright; iexists x'; iframe HR
    ispecialize Hr $$ %Φ
    iapply Hr; iexact Hc

theorem rtc_refl' (x : A) : ⊢ biRtc R x x :=
  (or_intro_left_trans (affinely_intro internalEq.refl)).trans (rtc_intro R x x)

theorem rtc_left' (x₁ x₂ x₃ : A) : R x₁ x₂ -∗ biRtc R x₂ x₃ -∗ biRtc R x₁ x₃ := by
  iintro H₁ H₂
  iapply rtc_intro
  unfold biRtcPre
  iright; iexists x₂; iframe

instance rtcNE (y : A) : NonExpansive (fun x => biRtc R x y) := NonExpansive₂.ne_left (biRtc R) y

instance tcNE (y : A) : NonExpansive (fun x => biTc R x y) :=
  inferInstanceAs (NonExpansive (bi_least_fixpoint (biTcPre R y)))

theorem tc_once' (x₁ x₂ : A) : R x₁ x₂ -∗ biTc R x₁ x₂ := by
  iintro H
  iapply tc_intro
  unfold biTcPre
  ileft
  iexact H

/-- Finite unrollings of the transitive-closure step (copy of W5c4). -/
def itT (x₂ : A) : Nat → A → PROP
  | 0, _ => iprop(False)
  | k+1, x => iprop(R x x₂ ∨ ∃ x', R x x' ∗ itT x₂ k x')

theorem itT_ne [NonExpansive₂ R] (x₂ : A) (k : Nat) : NonExpansive (itT R x₂ k) := by
  induction k with
  | zero => constructor; intros; exact Dist.rfl
  | succ k ih =>
    constructor; intro n x y h
    exact or_ne.ne (NonExpansive₂.ne h .rfl) (exists_ne fun _ => sep_ne.ne (NonExpansive₂.ne h .rfl) .rfl)

theorem muT_ne [NonExpansive₂ R] (x₂ : A) : NonExpansive (fun x => iprop(∃ k, itT R x₂ k x)) := by
  constructor; intro n x y h
  exact exists_ne fun k => (itT_ne R x₂ k).ne h

theorem tc_le_muT [NonExpansive₂ R] (x₂ x : A) : biTc R x x₂ ⊢ iprop(∃ k, itT R x₂ k x) := by
  letI := muT_ne R x₂
  iintro H
  ihave Hi := bi_tc_ind_left R x₂ (fun x => iprop(∃ k, itT R x₂ k x))
  ispecialize Hi $$ []
  · iintro !> %x₁ Hx
    icases Hx with ⟨Hx | ⟨%x', HR, Hk⟩⟩
    · iexists 1; simp only [itT]; ileft; iexact Hx
    · icases Hk with ⟨%k, Hk⟩
      iexists k+1; simp only [itT]; iright; iexists x'; iframe
  iapply Hi $$ %x H

theorem itT_le_tc (x₂ : A) (k : Nat) : ∀ x, itT R x₂ k x ⊢ biTc R x x₂ := by
  induction k with
  | zero => intro x; simp only [itT]; exact false_elim
  | succ k ih =>
    intro x
    simp only [itT]
    iintro H
    iapply tc_intro
    unfold biTcPre
    icases H with ⟨H | ⟨%x', HR, Hk⟩⟩
    · ileft; iexact H
    · iright; iexists x'; iframe HR; iapply (ih x'); iexact Hk

instance itT_timeless [∀ x y, Timeless (R x y)] (x₂ : A) (k : Nat) (x : A) : Timeless (itT R x₂ k x) := by
  induction k generalizing x with
  | zero => simp only [itT]; infer_instance
  | succ k ih => simp only [itT]; infer_instance

theorem tc_eq_muT [NonExpansive₂ R] (x x₂ : A) : biTc R x x₂ = iprop(∃ k, itT R x₂ k x) :=
  BIBase.BiEntails.to_eq ⟨tc_le_muT R x₂ x, exists_elim fun k => itT_le_tc R x₂ k x⟩

theorem tc_timeless' [NonExpansive₂ R] [∀ x y, Timeless (R x y)] (x y : A) : Timeless (biTc R x y) := by
  rw [tc_eq_muT]; infer_instance
end gen

theorem ne_of_disc {PROP : Type _} [Sbi PROP] {A : Type _} [OFE A] [OFE.Discrete A] (R : A → A → PROP) :
    NonExpansive₂ R := by
  constructor
  intro n x₁ x₂ hx y₁ y₂ hy
  have e1 : x₁ = x₂ := OFE.Discrete.discrete_0 (hx.le (Nat.zero_le n))
  have e2 : y₁ = y₂ := OFE.Discrete.discrete_0 (hy.le (Nat.zero_le n))
  subst e1; subst e2; exact Dist.rfl

theorem ieq_holds {A} [OFE A] {a b : A} {n} : (iprop(a ≡ b) : SiProp).holds n ↔ a ≡{n}≡ b := Iff.rfl
theorem aff_holds {P : SiProp} {n} : (iprop(<affine> P) : SiProp).holds n ↔ P.holds n :=
  ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩

/-- Relation true exactly when the source is 1 (not non-expansive on TN; copy of W5c4). -/
def R1 : TN → TN → SiProp := fun x _ => iprop(⌜x = ⟨1⟩⌝)
instance (x y : TN) : Timeless (R1 x y) := by unfold R1; infer_instance
instance : Timeless (iprop(emp) : SiProp) := ⟨fun n h => by
  cases n with
  | zero => exact .inr trivial
  | succ n => exact .inr trivial⟩

theorem r1_10 : ⊢ biRtc R1 ⟨1⟩ ⟨0⟩ := by
  ihave H := rtc_left' R1 ⟨1⟩ ⟨0⟩ ⟨0⟩
  iapply H
  · unfold R1; ipureintro; rfl
  · iapply rtc_refl'
theorem r1_20 : (biRtc R1 ⟨2⟩ ⟨0⟩).holds 0 :=
  ((rtcNE R1 ⟨0⟩).ne tn12 (Nat.le_refl 0)).mp (r1_10 0 trivial)
theorem tc_r1_10 : ⊢ biTc R1 ⟨1⟩ ⟨0⟩ := by
  ihave H := tc_once' R1 ⟨1⟩ ⟨0⟩
  iapply H
  unfold R1; ipureintro; rfl
theorem tc_r1_20 : (biTc R1 ⟨2⟩ ⟨0⟩).holds 0 :=
  ((tcNE R1 ⟨0⟩).ne tn12 (Nat.le_refl 0)).mp (tc_r1_10 0 trivial)

/-- R1 entails its pure content. -/
theorem r1_pure (x y : TN) : R1 x y ⊢ iprop(⌜x = ⟨1⟩⌝) := .rfl
theorem r1_pure2 (x y : TN) : R1 x y ⊢ (iprop(⌜x = ⟨1⟩ ∨ x = ⟨0⟩⌝) : SiProp) := fun _ h => Or.inl h
theorem aff_eq0 (x : TN) : iprop(<affine> (x ≡ (⟨0⟩ : TN))) ⊢ (iprop(⌜x = ⟨1⟩ ∨ x = ⟨0⟩⌝) : SiProp) := fun n h => by
  refine Or.inr ?_
  cases x with | mk v =>
  have h' : min v (n+1) = min 0 (n+1) := aff_holds.mp h
  simp only [TN.mk.injEq]; omega

/-- The least non-expansive predicate containing 1: 1 at every step, every positive number at step 0. -/
def psi (x : TN) : SiProp := ⟨fun n => x.v = 1 ∨ (n = 0 ∧ 1 ≤ x.v), fun h hle => by omega⟩
instance psiNE : NonExpansive psi := ⟨fun {n x y} h {m} hm => by
  have h' : min x.v (n+1) = min y.v (n+1) := h
  show (x.v = 1 ∨ (m = 0 ∧ 1 ≤ x.v)) ↔ (y.v = 1 ∨ (m = 0 ∧ 1 ≤ y.v))
  constructor <;> intro hh <;> omega⟩
theorem r1_psi (x y : TN) : R1 x y ⊢ psi x := fun _ (h : x = ⟨1⟩) => Or.inl (congrArg TN.v h)
theorem tc_r1_psi (x : TN) : biTc R1 x ⟨0⟩ ⊢ psi x := by
  iintro H
  ihave Hi := bi_tc_ind_left R1 ⟨0⟩ psi
  ispecialize Hi $$ []
  · iintro !> %x₁ Hx
    icases Hx with ⟨Hx | ⟨%x', Hx, -⟩⟩
    · iapply (r1_psi x₁ ⟨0⟩); iexact Hx
    · iapply (r1_psi x₁ x'); iexact Hx
  iapply Hi $$ %x H
theorem tc_r1_21 : ¬ (biTc R1 ⟨2⟩ ⟨0⟩).holds 1 := fun h => by
  have := tc_r1_psi ⟨2⟩ 1 h
  simp [psi] at this
end J1c0

namespace J1c0
open Iris Iris.HeapLang Iris.Std Iris.ProgramLogic Iris.ProgramLogic.Language Iris.ProgramLogic.EctxLanguage Iris.ProgramLogic.EctxItemLanguage FromMathlib
theorem alloc_ne (l : Loc) (n : Int) (v : Option Val) (hn : 0 < n) :
    (default : HeapLang.State).initHeap l n v ≠ default := fun hσ => by
  have := congrArg (fun σ : HeapLang.State => σ.get? l) hσ
  simp only [State.get?] at this
  rw [get?_foldl_insert, ite_eq_left ⟨0, by omega, by simp [loc_add_zero]⟩] at this
  simp [default, get?_empty] at this
theorem proph_ne (p : ProphId) :
    ({ heap := (default : HeapLang.State).heap, usedProphId := (default : HeapLang.State).usedProphId.insert p } : HeapLang.State) ≠ default := fun hσ => by
  have := congrArg (fun σ : HeapLang.State => p ∈ σ.usedProphId) hσ
  simp [default] at this
end J1c0

namespace J1c0
open Iris Iris.BI Iris.Std Iris.Algebra
-- helper: Bool with xor (copied from W4c5): UPred X2 is non-affine and not positive
inductive X2 | o | i deriving DecidableEq
def X2.op : X2 → X2 → X2
  | .o, y => y
  | .i, .o => .i
  | .i, .i => .o
instance : OFE X2 := OFE.ofDiscrete X2
instance : OFE.Discrete X2 := ⟨id⟩
instance x2ORA : ORA X2 := ORA.ofDiscreteORAData {
  pcore := fun _ => some .o
  op := X2.op
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
  pcore_mono := by intro x y cx h1 h2; exact ⟨.o, rfl, by cases h2; rfl⟩
  pcore_order_op := by intro x cx h y; exact ⟨.o, rfl, by cases h; rfl⟩
  pcore_increasing := by intro x cx h y; cases h; rfl
  increasing_closed := by intro x y _ h; cases h; assumption }
instance : OrderRefl X2 := ⟨fun x => show x = x from rfl⟩
instance x2UORA : UORA X2 where
  unit := .o
  unit_valid := trivial
  unit_left_id := rfl
  pcore_unit := rfl
abbrev oI : UPred X2 := UPred.ownM X2.i
end J1c0

open Iris Iris.BI Iris.OFE Iris.Algebra Iris.Std J1c0
open Iris.HeapLang Iris.ProgramLogic Iris.ProgramLogic.Language Iris.ProgramLogic.EctxLanguage Iris.ProgramLogic.EctxItemLanguage

namespace J1c0

-- `FromMathlib.Pairwise.forall` idx 4, 6: jointly removable (hR alone turns the goal R a b into the premise a ≠ b; the list facts are unused)
theorem j1_1 : drop2% FromMathlib.Pairwise.forall 4 6 := by
  intros; simp_all

-- `FromMathlib.Pairwise.forall` idx 4, 8: jointly removable (hR alone turns the goal R a b into the premise a ≠ b; the list facts are unused)
theorem j1_2 : drop2% FromMathlib.Pairwise.forall 4 8 := by
  intros; simp_all

-- `FromMathlib.Pairwise.forall` idx 6, 8: jointly removable (hR alone turns the goal R a b into the premise a ≠ b; the list facts are unused)
theorem j1_3 : drop2% FromMathlib.Pairwise.forall 6 8 := by
  intros; simp_all

-- `Iris.Agree.agree_map_ext` idx 6, 7: not jointly removable (TN, f = g = bad: H holds but bad is not non-expansive (1, 2 are 0-close, images 0, 1 are not))
theorem j1_4 : ¬ indep2_0% Iris.Agree.agree_map_ext 6 7 := fun h => by
  have := (@h TN TN _ _ bad bad (AA [0]) (fun _ => rfl)).1.ne (n := 0) (x₁ := ⟨1⟩) (x₂ := ⟨2⟩) tn12
  simp [tn_dist, bad] at this

-- `Iris.Algebra.BigOpM.bigOpM_gen_proper_2` idx 15, 16: not jointly removable (R = empty relation (vacuously a congruence), m1 = m2 = ∅: R unit unit fails)
theorem j1_5 : ¬ drop2_0% Iris.Algebra.BigOpM.bigOpM_gen_proper_2 15 16 := fun h =>
  @h Nat _ ad 0 addMon TM Nat _ Nat Nat (fun _ _ => False) (fun _ _ => 0) (fun _ _ => 0) ∅ ∅
    (fun e _ => e) (fun _ => rfl) (fun e _ => (emptyGet e).elim)

-- `Iris.BI.MonPred.monPred_at_hom` idx 8, 11: not jointly removable (UIdx, SiProp, op₁ = op₂ = ∗, u₁ = emp, u₂ = False: hop holds by rfl but emp at 0 is not False)
theorem j1_6 : ¬ indep2_0% Iris.BI.MonPred.monPred_at_hom 8 11 := fun h => by
  have H := @h UIdx SiProp _ BIBase.sep BIBase.sep iprop(emp) iprop(False) inferInstance (0 : Nat) (fun {_ _} => rfl)
  exact cast (congrArg (fun P : SiProp => P.holds 0) H.2) trivial

-- `Iris.BI.plainly_sep_weak_homomorphism` idx 2, 3: not jointly removable (non-positive UPred X2 (xor), x = y = ownM i: ■ (x ∗ y) holds at the unit, ■ x ∗ ■ y does not)
theorem j1_7 : ¬ drop2_0% Iris.BI.plainly_sep_weak_homomorphism 2 3 := fun h => by
  have H := ((@h (UPred X2) _).map_op (x := oI) (y := oI)).1 0 ⟨.o, trivial⟩ ⟨.i, .i, rfl, rfl, rfl⟩
  obtain ⟨_, _, _, h1, _⟩ := H
  cases h1

-- `Iris.HeapLang.mk_pure_prim_step` idx 3, 4: jointly removable (determinism follows by case analysis on base steps (impure rules contradict hstep at the empty state) and subredexes are values by base_ctx_step_val, both from hstep)
theorem j1_8 : drop2% Iris.HeapLang.mk_pure_prim_step 3 4 := fun {e1 e2} hstep => by
  refine mk_pure_prim_step hstep (fun {σ1 κs e2' σ2 efs} hb => ?_)
    (subredexes_are_values fun Ki e' heq => base_ctx_step_val (heq ▸ hstep default))
  obtain ⟨σ', κ0, ef0, hσ, hκ, hef, h0⟩ : ∃ σ' κ0 ef0, σ' = (default : HeapLang.State) ∧ κ0 = [] ∧ ef0 = [] ∧ BaseStep e1 default κ0 e2 σ' ef0 :=
    ⟨_, _, _, rfl, rfl, rfl, hstep default⟩
  cases hb <;> cases h0 <;> simp_all
  all_goals exfalso
  all_goals first
    | (simp_all [State.get?, default, get?_empty]; done)
    | exact alloc_ne _ _ _ (by assumption) hσ
    | exact proph_ne _ hσ

-- `Iris.Inv.A_alloc` idx 2, 6: jointly removable (sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; affinity, persistence of inv, fupd_intro and fupd_frame_left all unused)
theorem j1_9 : drop2% Iris.Inv.A_alloc 2 6 := by
  intro PROP _ fupd name inv _ hm hff _ hmm hia gname start finished sts
  exact sa_core fupd name inv hm hff hmm hia gname start finished sts (fun γ => Iris.Inv.A fupd name inv gname start finished γ)

-- `Iris.Inv.A_alloc` idx 2, 7: jointly removable (sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; affinity, persistence of inv, fupd_intro and fupd_frame_left all unused)
theorem j1_10 : drop2% Iris.Inv.A_alloc 2 7 := by
  intro PROP _ fupd name inv _ hm hff _ hmm hia gname start finished sts
  exact sa_core fupd name inv hm hff hmm hia gname start finished sts (fun γ => Iris.Inv.A fupd name inv gname start finished γ)

-- `Iris.Inv.A_alloc` idx 2, 10: jointly removable (sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; affinity, persistence of inv, fupd_intro and fupd_frame_left all unused)
theorem j1_11 : drop2% Iris.Inv.A_alloc 2 10 := by
  intro PROP _ fupd name inv _ _ hm hff hmm hia gname start finished sts
  exact sa_core fupd name inv hm hff hmm hia gname start finished sts (fun γ => Iris.Inv.A fupd name inv gname start finished γ)

-- `Iris.Inv.A_alloc` idx 6, 7: jointly removable (sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; affinity, persistence of inv, fupd_intro and fupd_frame_left all unused)
theorem j1_12 : drop2% Iris.Inv.A_alloc 6 7 := by
  intro PROP _ _ fupd name inv hm hff _ hmm hia gname start finished sts
  exact sa_core fupd name inv hm hff hmm hia gname start finished sts (fun γ => Iris.Inv.A fupd name inv gname start finished γ)

-- `Iris.Inv.A_alloc` idx 6, 10: jointly removable (sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; affinity, persistence of inv, fupd_intro and fupd_frame_left all unused)
theorem j1_13 : drop2% Iris.Inv.A_alloc 6 10 := by
  intro PROP _ _ fupd name inv _ hm hff hmm hia gname start finished sts
  exact sa_core fupd name inv hm hff hmm hia gname start finished sts (fun γ => Iris.Inv.A fupd name inv gname start finished γ)

-- `Iris.Inv.A_alloc` idx 7, 10: jointly removable (sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; affinity, persistence of inv, fupd_intro and fupd_frame_left all unused)
theorem j1_14 : drop2% Iris.Inv.A_alloc 7 10 := by
  intro PROP _ _ fupd name inv _ hm hff hmm hia gname start finished sts
  exact sa_core fupd name inv hm hff hmm hia gname start finished sts (fun γ => Iris.Inv.A fupd name inv gname start finished γ)

-- `Iris.Inv.inv_fupd'` idx 2, 8: jointly removable (inv_fupd with Q the wand and wand elimination, then fupd_fupd; neither affinity nor persistence of inv used)
theorem j1_15 : drop2% Iris.Inv.inv_fupd' 2 8 := by
  intro PROP _ P R fupd name inv hff hinv i
  exact (@hinv i P _ _ wand_elim_right).trans hff

-- `Iris.Inv.saved_alloc` idx 2, 6: jointly removable (sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; affinity, persistence of inv, fupd_intro and fupd_frame_left all unused)
theorem j1_16 : drop2% Iris.Inv.saved_alloc 2 6 := by
  intro PROP _ fupd name inv _ hm hff _ hmm hia gname start finished sts P
  exact sa_core fupd name inv hm hff hmm hia gname start finished sts P

-- `Iris.Inv.saved_alloc` idx 2, 7: jointly removable (sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; affinity, persistence of inv, fupd_intro and fupd_frame_left all unused)
theorem j1_17 : drop2% Iris.Inv.saved_alloc 2 7 := by
  intro PROP _ fupd name inv _ hm hff _ hmm hia gname start finished sts P
  exact sa_core fupd name inv hm hff hmm hia gname start finished sts P

-- `Iris.Inv.saved_alloc` idx 2, 10: jointly removable (sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; affinity, persistence of inv, fupd_intro and fupd_frame_left all unused)
theorem j1_18 : drop2% Iris.Inv.saved_alloc 2 10 := by
  intro PROP _ fupd name inv _ _ hm hff hmm hia gname start finished sts P
  exact sa_core fupd name inv hm hff hmm hia gname start finished sts P

-- `Iris.Inv.saved_alloc` idx 6, 7: jointly removable (sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; affinity, persistence of inv, fupd_intro and fupd_frame_left all unused)
theorem j1_19 : drop2% Iris.Inv.saved_alloc 6 7 := by
  intro PROP _ _ fupd name inv hm hff _ hmm hia gname start finished sts P
  exact sa_core fupd name inv hm hff hmm hia gname start finished sts P

-- `Iris.Inv.saved_alloc` idx 6, 10: jointly removable (sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; affinity, persistence of inv, fupd_intro and fupd_frame_left all unused)
theorem j1_20 : drop2% Iris.Inv.saved_alloc 6 10 := by
  intro PROP _ _ fupd name inv _ hm hff hmm hia gname start finished sts P
  exact sa_core fupd name inv hm hff hmm hia gname start finished sts P

-- `Iris.Inv.saved_alloc` idx 7, 10: jointly removable (sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; affinity, persistence of inv, fupd_intro and fupd_frame_left all unused)
theorem j1_21 : drop2% Iris.Inv.saved_alloc 7 10 := by
  intro PROP _ _ fupd name inv _ hm hff hmm hia gname start finished sts P
  exact sa_core fupd name inv hm hff hmm hia gname start finished sts P

-- `Iris.LaterCreditsPlain.contradiction` idx 2, 8: jointly removable (BILoeb comes from Sbi by instance resolution; laterN_False holds without BIPersistentlyExist (weak Löb), then lc_fupd_elim_later_keep induction)
theorem j1_22 : drop2% Iris.LaterCreditsPlain.contradiction 2 8 := by
  intro PROP _ _ lc lc_fupd_elim_later lc_soundness fupd_keep_si_pure'
  apply pure_soundness (PROP := PROP)
  apply lc_soundness _ ⊤
  refine (sep_emp.2.trans (sep_mono_right laterNFalse_gen)).trans
    (sep_exists_left.1.trans (exists_elim fun n => ?_))
  induction n with
  | zero => exact sep_comm.1.trans (wand_elim false_elim)
  | succ n ih =>
    have k := Iris.LaterCreditsPlain.lc_fupd_elim_later_keep lc_fupd_elim_later fupd_keep_si_pure'
      (E := ⊤) (P := iprop(▷^[n] False))
    exact (wand_elim (emp_sep.2.trans (wand_elim k))).trans ((BIFUpdate.mono ih).trans BIFUpdate.trans)

-- `Iris.LaterCreditsPlain.laterN_False` idx 2, 3: jointly removable (BILoeb comes from Sbi by instance resolution; weak Löb on the existential needs no BIPersistentlyExist)
theorem j1_23 : drop2% Iris.LaterCreditsPlain.laterN_False 2 3 := by
  intro PROP _
  exact laterNFalse_gen

-- `Iris.OFE.Iso.ext` idx 6, 7: not jointly removable (DB, the identity iso and the negation iso are different)
theorem j1_24 : ¬ drop2_0% Iris.OFE.Iso.ext 6 7 := fun h => by
  have := congrArg (fun x : Iso DB DB => (x.hom.f ⟨true⟩).v) (@h DB DB _ _ isoId isoNot)
  simp [isoId, isoNot, homNot, notDB, Hom.id] at this

-- `Iris.SavedProp.contradiction` idx 2, 3: jointly removable (saved_NA and saved_A hold from agree and persistence of saved alone, so the allocated proposition is False; alloc plus consistency; no bupd law, affinity or BIPersistentlyExist used)
theorem j1_25 : drop2% Iris.SavedProp.contradiction 2 3 := by
  intro PROP _ bupd ident saved _ _ _ _ _ alloc agree cons
  exact sp_contra bupd ident saved alloc agree cons

-- `Iris.SavedProp.contradiction` idx 2, 8: jointly removable (saved_NA and saved_A hold from agree and persistence of saved alone, so the allocated proposition is False; alloc plus consistency; no bupd law, affinity or BIPersistentlyExist used)
theorem j1_26 : drop2% Iris.SavedProp.contradiction 2 8 := by
  intro PROP _ _ bupd ident saved _ _ _ _ alloc agree cons
  exact sp_contra bupd ident saved alloc agree cons

-- `Iris.SavedProp.contradiction` idx 2, 9: jointly removable (saved_NA and saved_A hold from agree and persistence of saved alone, so the allocated proposition is False; alloc plus consistency; no bupd law, affinity or BIPersistentlyExist used)
theorem j1_27 : drop2% Iris.SavedProp.contradiction 2 9 := by
  intro PROP _ _ bupd ident saved _ _ _ _ alloc agree cons
  exact sp_contra bupd ident saved alloc agree cons

-- `Iris.SavedProp.contradiction` idx 2, 10: jointly removable (saved_NA and saved_A hold from agree and persistence of saved alone, so the allocated proposition is False; alloc plus consistency; no bupd law, affinity or BIPersistentlyExist used)
theorem j1_28 : drop2% Iris.SavedProp.contradiction 2 10 := by
  intro PROP _ _ bupd ident saved _ _ _ _ alloc agree cons
  exact sp_contra bupd ident saved alloc agree cons

-- `Iris.SavedProp.contradiction` idx 2, 11: jointly removable (saved_NA and saved_A hold from agree and persistence of saved alone, so the allocated proposition is False; alloc plus consistency; no bupd law, affinity or BIPersistentlyExist used)
theorem j1_29 : drop2% Iris.SavedProp.contradiction 2 11 := by
  intro PROP _ _ bupd ident saved _ _ _ _ alloc agree cons
  exact sp_contra bupd ident saved alloc agree cons

-- `Iris.SavedProp.contradiction` idx 3, 8: jointly removable (saved_NA and saved_A hold from agree and persistence of saved alone, so the allocated proposition is False; alloc plus consistency; no bupd law, affinity or BIPersistentlyExist used)
theorem j1_30 : drop2% Iris.SavedProp.contradiction 3 8 := by
  intro PROP _ _ bupd ident saved _ _ _ _ alloc agree cons
  exact sp_contra bupd ident saved alloc agree cons

-- `Iris.SavedProp.contradiction` idx 3, 9: jointly removable (saved_NA and saved_A hold from agree and persistence of saved alone, so the allocated proposition is False; alloc plus consistency; no bupd law, affinity or BIPersistentlyExist used)
theorem j1_31 : drop2% Iris.SavedProp.contradiction 3 9 := by
  intro PROP _ _ bupd ident saved _ _ _ _ alloc agree cons
  exact sp_contra bupd ident saved alloc agree cons

-- `Iris.SavedProp.contradiction` idx 3, 10: jointly removable (saved_NA and saved_A hold from agree and persistence of saved alone, so the allocated proposition is False; alloc plus consistency; no bupd law, affinity or BIPersistentlyExist used)
theorem j1_32 : drop2% Iris.SavedProp.contradiction 3 10 := by
  intro PROP _ _ bupd ident saved _ _ _ _ alloc agree cons
  exact sp_contra bupd ident saved alloc agree cons

-- `Iris.SavedProp.contradiction` idx 3, 11: jointly removable (saved_NA and saved_A hold from agree and persistence of saved alone, so the allocated proposition is False; alloc plus consistency; no bupd law, affinity or BIPersistentlyExist used)
theorem j1_33 : drop2% Iris.SavedProp.contradiction 3 11 := by
  intro PROP _ _ bupd ident saved _ _ _ _ alloc agree cons
  exact sp_contra bupd ident saved alloc agree cons

-- `Iris.SavedProp.contradiction` idx 8, 9: jointly removable (saved_NA and saved_A hold from agree and persistence of saved alone, so the allocated proposition is False; alloc plus consistency; no bupd law, affinity or BIPersistentlyExist used)
theorem j1_34 : drop2% Iris.SavedProp.contradiction 8 9 := by
  intro PROP _ _ _ bupd ident saved _ _ _ alloc agree cons
  exact sp_contra bupd ident saved alloc agree cons

-- `Iris.SavedProp.contradiction` idx 8, 10: jointly removable (saved_NA and saved_A hold from agree and persistence of saved alone, so the allocated proposition is False; alloc plus consistency; no bupd law, affinity or BIPersistentlyExist used)
theorem j1_35 : drop2% Iris.SavedProp.contradiction 8 10 := by
  intro PROP _ _ _ bupd ident saved _ _ _ alloc agree cons
  exact sp_contra bupd ident saved alloc agree cons

-- `Iris.SavedProp.contradiction` idx 8, 11: jointly removable (saved_NA and saved_A hold from agree and persistence of saved alone, so the allocated proposition is False; alloc plus consistency; no bupd law, affinity or BIPersistentlyExist used)
theorem j1_36 : drop2% Iris.SavedProp.contradiction 8 11 := by
  intro PROP _ _ _ bupd ident saved _ _ _ alloc agree cons
  exact sp_contra bupd ident saved alloc agree cons

-- `Iris.SavedProp.contradiction` idx 9, 10: jointly removable (saved_NA and saved_A hold from agree and persistence of saved alone, so the allocated proposition is False; alloc plus consistency; no bupd law, affinity or BIPersistentlyExist used)
theorem j1_37 : drop2% Iris.SavedProp.contradiction 9 10 := by
  intro PROP _ _ _ bupd ident saved _ _ _ alloc agree cons
  exact sp_contra bupd ident saved alloc agree cons

-- `Iris.SavedProp.contradiction` idx 9, 11: jointly removable (saved_NA and saved_A hold from agree and persistence of saved alone, so the allocated proposition is False; alloc plus consistency; no bupd law, affinity or BIPersistentlyExist used)
theorem j1_38 : drop2% Iris.SavedProp.contradiction 9 11 := by
  intro PROP _ _ _ bupd ident saved _ _ _ alloc agree cons
  exact sp_contra bupd ident saved alloc agree cons

-- `Iris.SavedProp.contradiction` idx 10, 11: jointly removable (saved_NA and saved_A hold from agree and persistence of saved alone, so the allocated proposition is False; alloc plus consistency; no bupd law, affinity or BIPersistentlyExist used)
theorem j1_39 : drop2% Iris.SavedProp.contradiction 10 11 := by
  intro PROP _ _ _ bupd ident saved _ _ _ alloc agree cons
  exact sp_contra bupd ident saved alloc agree cons

-- `Iris.SavedProp.saved_A` idx 2, 3: jointly removable (agree makes saved affine, so with persistence saved i (A i) is intuitionistic; saved_NA without BIAffine/BIPersistentlyExist)
theorem j1_40 : drop2% Iris.SavedProp.saved_A 2 3 := by
  intro PROP _ ident saved _ agree i
  exact savedA_pers ident saved agree i

-- `Iris.SavedProp.saved_NA` idx 2, 3: jointly removable (persistence of saved plus affinity from agree; only ∧-reasoning)
theorem j1_41 : drop2% Iris.SavedProp.saved_NA 2 3 := by
  intro PROP _ ident saved _ agree i
  exact savedNA_pers ident saved agree i

-- `Iris.SavedProp.saved_NA` idx 2, 6: jointly removable (with BIAffine both halves of the boxed separating conjunction are available; only ∧-reasoning)
theorem j1_42 : drop2% Iris.SavedProp.saved_NA 2 6 := by
  intro PROP _ _ ident saved agree i
  exact savedNA_aff ident saved agree i

-- `Iris.SavedProp.saved_NA` idx 3, 6: jointly removable (agree makes saved affine; the boxed sep gives <pers> ¬P and <pers> A, and with saved i (A i) the agreement under <pers> (stray ¬P absorbed); all meet under <pers>, giving <pers> False)
theorem j1_43 : drop2% Iris.SavedProp.saved_NA 3 6 := by
  intro PROP _ _ ident saved agree i
  exact savedNA_gen ident saved agree i

-- `Iris.bi_rtc_strong_ind_left` idx 5, 8: not jointly removable (SiProp, TN, R x _ = ⌜x = 1⌝, x₂ = 0, Φ x = ⌜x = 1 ∨ x = 0⌝ (closed, not NE): biRtc R 2 0 holds at step 0 but Φ 2 does not)
theorem j1_44 : ¬ drop2_0% Iris.bi_rtc_strong_ind_left 5 8 := fun h => by
  have Hcl : ⊢ (iprop(□ (∀ x₁, <affine> (x₁ ≡ (⟨0⟩ : TN)) ∨ (∃ x', R1 x₁ x' ∗ (iprop(⌜x' = ⟨1⟩ ∨ x' = ⟨0⟩⌝) ∧ biRtc R1 x' ⟨0⟩)) -∗ iprop(⌜x₁ = ⟨1⟩ ∨ x₁ = ⟨0⟩⌝))) : SiProp) := by
    iintro !> %x₁ Hx
    icases Hx with ⟨Hx | ⟨%x', Hx, -⟩⟩
    · iapply (aff_eq0 x₁); iexact Hx
    · iapply (r1_pure2 x₁ x'); iexact Hx
  have E := wand_entails ((Hcl.trans (wand_entails (@h SiProp TN _ _ R1 ⟨0⟩ (fun x => iprop(⌜x = ⟨1⟩ ∨ x = ⟨0⟩⌝))))).trans
    (forall_elim (Ψ := fun x₁ => iprop(biRtc R1 x₁ ⟨0⟩ -∗ ⌜x₁ = ⟨1⟩ ∨ x₁ = ⟨0⟩⌝)) ⟨2⟩))
  have := E 0 r1_20
  simp at this

-- `Iris.bi_tc_strong_ind_left` idx 5, 8: not jointly removable (SiProp, TN, R x _ = ⌜x = 1⌝, x₂ = 0, Φ x = ⌜x = 1⌝ (closed, not NE): biTc R 2 0 holds at step 0 but Φ 2 does not)
theorem j1_45 : ¬ drop2_0% Iris.bi_tc_strong_ind_left 5 8 := fun h => by
  have Hcl : ⊢ (iprop(□ (∀ x₁, R1 x₁ ⟨0⟩ ∨ (∃ x', R1 x₁ x' ∗ (iprop(⌜x' = ⟨1⟩⌝) ∧ biTc R1 x' ⟨0⟩)) -∗ iprop(⌜x₁ = ⟨1⟩⌝))) : SiProp) := by
    iintro !> %x₁ Hx
    icases Hx with ⟨Hx | ⟨%x', Hx, -⟩⟩
    · iapply (r1_pure x₁ ⟨0⟩); iexact Hx
    · iapply (r1_pure x₁ x'); iexact Hx
  have E := wand_entails ((Hcl.trans (wand_entails (@h SiProp TN _ _ R1 ⟨0⟩ (fun x => iprop(⌜x = ⟨1⟩⌝))))).trans
    (forall_elim (Ψ := fun x₁ => iprop(biTc R1 x₁ ⟨0⟩ -∗ ⌜x₁ = ⟨1⟩⌝)) ⟨2⟩))
  have := E 0 tc_r1_20
  simp at this

-- `Iris.bi_tc_timeless` idx 3, 5: jointly removable (given NonExpansive₂ R, biTc R x y = ∃ k, k-fold unrolling built from timeless R by ∨, ∃, ∗, False: neither emp nor internal equality occurs)
theorem j1_46 : drop2% Iris.bi_tc_timeless 3 5 := by
  intro PROP A _ _ R _ _ x y; exact tc_timeless' R x y

-- `Iris.bi_tc_timeless` idx 3, 7: jointly removable (Discrete A makes R NonExpansive₂; then biTc R x y is the timeless k-fold unrolling (emp does not occur))
theorem j1_47 : drop2% Iris.bi_tc_timeless 3 7 := by
  intro PROP A _ _ _ R _ x y; exact @tc_timeless' PROP _ A _ R (ne_of_disc R) _ x y

-- `Iris.bi_tc_timeless` idx 5, 7: not jointly removable (SiProp (emp timeless), TN, R x _ = ⌜x = 1⌝ (timeless, not NE): biTc R 2 0 holds at step 0 but not at step 1)
theorem j1_48 : ¬ drop2_0% Iris.bi_tc_timeless 5 7 := fun h => by
  have H := (@h SiProp TN _ _ _ R1 _ ⟨2⟩ ⟨0⟩).timeless 1 (show (biTc R1 ⟨2⟩ ⟨0⟩).holds 0 from tc_r1_20)
  rcases H with H | H
  · exact H
  · exact tc_r1_21 H

-- `Iris.fixpointK_proper` idx 6, 7: not jointly removable (CS, k = 0, f = g = id: the identity is not contractive)
theorem j1_49 : ¬ indep2_0% Iris.fixpointK_proper 6 7 := fun h =>
  id_not_contr (@h CS _ _ 0 id id ⟨fun {_ _ _} h => h⟩ (fun _ => rfl)).1

-- `Iris.fixpointK_proper` idx 6, 8: not jointly removable (CS, k = 2, f = g = kf: kf∘kf is constant (contractive) but kf is not non-expansive)
theorem j1_50 : ¬ indep2_0% Iris.fixpointK_proper 6 8 := fun h =>
  kf_not_ne (@h CS _ _ 2 kf kf kfC (fun _ => rfl)).2

-- `Iris.fixpointK_proper` idx 7, 8: not jointly removable (CS, k = 2, f = g = kf: kf∘kf is constant (contractive) but kf is not non-expansive)
theorem j1_51 : ¬ indep2_0% Iris.fixpointK_proper 7 8 := fun h =>
  kf_not_ne (@h CS _ _ 2 kf kf kfC (fun _ => rfl)).2

-- `Iris.fixpoint_proper` idx 5, 6: not jointly removable (CS, f = g = id: the identity is not contractive)
theorem j1_52 : ¬ indep2_0% Iris.fixpoint_proper 5 6 := fun h =>
  id_not_contr (@h CS _ _ id id (fun _ => rfl)).1

-- `View.map_ne` idx 14, 15: jointly removable (the proof only needs pointwise f1 a =n= f2 a for Agree.map'; neither NonExpansive instance is used)
theorem j1_53 : drop2% View.map_ne 14 15 := by
  intro A B A' B' _ _ _ R R' n f1 f2 g1 g2 v h1 h2
  refine ⟨?_, h2 _⟩
  simp only [View.map]
  split
  · rfl
  · refine ⟨rfl, ?_⟩
    rename_i a _
    exact a.ind fun _ => by
      refine Agree.dist_mk.mpr ⟨?_, ?_⟩ <;> simp only [Agree.Raw.map'_car, List.mem_map] <;> rintro _ ⟨a, ha, rfl⟩
      · exact ⟨f2 a, ⟨a, ha, rfl⟩, h1 a⟩
      · exact ⟨f1 a, ⟨a, ha, rfl⟩, h1 a⟩

-- `_private.Iris.BI.BigOp.BigSepList.0.Iris.BI.BigSepL2.zip_set` idx 5, 6: jointly removable (zip and set commute for every index (out of range both sides are unchanged); induction on the lists)
theorem j1_54 : drop2% _private.Iris.BI.BigOp.BigSepList.«0».Iris.BI.BigSepL2.zip_set 5 6 := by
  intro C D l1 l2 i y1 y2
  exact zipSet l1 l2 i y1 y2

end J1c0
