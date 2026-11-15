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
namespace T1c2
open Iris Iris.BI


/-- Branching Kripke frame: none below some true and some false. -/
def wle (a b : Option Bool) : Prop := a = none ∨ a = b
theorem wle_refl (a : Option Bool) : wle a a := .inr rfl
theorem wle_trans {a b c : Option Bool} (h1 : wle a b) (h2 : wle b c) : wle a c := by
  rcases h1 with h1 | h1
  · exact .inl h1
  · subst h1; exact h2

/-- KW: intuitionistic Kripke BI of up-closed predicates on the branching frame; sep = and,
persistently = later = id (affine, everything persistent, BIPersistentlyExist). -/
structure KW where
  p : Option Bool → Prop
  mono : ∀ {a b}, wle a b → p a → p b

theorem KW.ext' {P Q : KW} (h : ∀ n, P.p n ↔ Q.p n) : P = Q := by
  cases P; cases Q; congr; funext n; exact propext (h n)

instance : COFE KW := COFE.ofDiscrete _

instance kwBase : BIBase KW where
  Entails P Q := ∀ n, P.p n → Q.p n
  emp := ⟨fun _ => True, fun _ h => h⟩
  pure φ := ⟨fun _ => φ, fun _ h => h⟩
  and P Q := ⟨fun n => P.p n ∧ Q.p n, fun h x => ⟨P.mono h x.1, Q.mono h x.2⟩⟩
  or P Q := ⟨fun n => P.p n ∨ Q.p n, fun h x => x.imp (P.mono h) (Q.mono h)⟩
  imp P Q := ⟨fun n => ∀ m, wle n m → P.p m → Q.p m, fun h x m hm => x m (wle_trans h hm)⟩
  sForall Ψ := ⟨fun n => ∀ p, Ψ p → KW.p p n, fun h x p hp => p.mono h (x p hp)⟩
  sExists Ψ := ⟨fun n => ∃ p, Ψ p ∧ KW.p p n, fun h ⟨p, hp, x⟩ => ⟨p, hp, p.mono h x⟩⟩
  sep P Q := ⟨fun n => P.p n ∧ Q.p n, fun h x => ⟨P.mono h x.1, Q.mono h x.2⟩⟩
  wand P Q := ⟨fun n => ∀ m, wle n m → P.p m → Q.p m, fun h x m hm => x m (wle_trans h hm)⟩
  persistently P := P
  later P := P

instance kwBI : BI KW where
  entails_refl _ h := h
  entails_trans h1 h2 x h := h2 x (h1 x h)
  equiv_iff {P Q} := ⟨fun h => h ▸ ⟨fun _ h => h, fun _ h => h⟩,
    fun ⟨h₁, h₂⟩ => KW.ext' fun n => ⟨h₁ n, h₂ n⟩⟩
  and_ne          := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  or_ne           := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  imp_ne          := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  sep_ne          := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  wand_ne         := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  persistently_ne := ⟨by rintro _ _ _ h; exact (h : _ = _) ▸ rfl⟩
  later_ne        := ⟨by rintro _ _ _ h; exact (h : _ = _) ▸ rfl⟩
  sForall_ne {_ P Q} h := (liftRel_eq.1 (h : liftRel Eq P Q)) ▸ rfl
  sExists_ne {_ P Q} h := (liftRel_eq.1 (h : liftRel Eq P Q)) ▸ rfl
  pure_intro h _ _ := h
  pure_elim' h n hφ := h hφ n trivial
  and_elim_l _ h := h.1
  and_elim_r _ h := h.2
  and_intro h1 h2 x h := ⟨h1 x h, h2 x h⟩
  or_intro_l _ h := .inl h
  or_intro_r _ h := .inr h
  or_elim h1 h2 x h := h.elim (h1 x) (h2 x)
  imp_intro {P Q R} h n hP m hm hQ := h m ⟨P.mono hm hP, hQ⟩
  imp_elim h n hPQ := h n hPQ.1 n (wle_refl n) hPQ.2
  sForall_intro h x hP p hp := h p hp x hP
  sForall_elim hp _ h := h _ hp
  sExists_intro hp _ h := ⟨_, hp, h⟩
  sExists_elim h x := fun ⟨p, hp, hx⟩ => h p hp x hx
  sep_mono h1 h2 x h := ⟨h1 x h.1, h2 x h.2⟩
  emp_sep := ⟨fun _ h => h.2, fun _ h => ⟨trivial, h⟩⟩
  sep_symm _ h := ⟨h.2, h.1⟩
  sep_assoc_l _ h := ⟨h.1.1, h.1.2, h.2⟩
  wand_intro {P Q R} h n hP m hm hQ := h m ⟨P.mono hm hP, hQ⟩
  wand_elim h n hPQ := h n hPQ.1 n (wle_refl n) hPQ.2
  persistently_mono h x hP := h x hP
  persistently_idem_2 _ h := h
  persistently_emp_2 _ _ := trivial
  persistently_and_2 _ h := h
  persistently_absorb_l _ h := h.1
  persistently_and_l _ h := ⟨h.1, h.2⟩
  later_mono h := h
  later_intro _ h := h
  later_sForall_2 n h p hp := h _ ⟨p, rfl⟩ n (wle_refl n) hp
  later_sExists_false _ := fun ⟨p, hp⟩ => .inr ⟨_, ⟨_, rfl⟩, hp⟩
  later_sep := ⟨fun _ h => h, fun _ h => h⟩
  later_persistently := ⟨fun _ h => h, fun _ h => h⟩
  later_false_em _ _ := .inr fun _ _ hf => hf.elim

instance kwAffine : BIAffine KW := ⟨fun _ => ⟨fun _ _ => trivial⟩⟩
instance kwPers (P : KW) : Persistent P := ⟨fun _ h => h⟩
instance kwPE : BIPersistentlyExist KW := ⟨fun _ _ ⟨p, hp, h⟩ => ⟨_, ⟨p, rfl⟩, hp, h⟩⟩

/-- The proposition holding exactly at the leaf `some b`. -/
def kwAt (b : Bool) : KW := ⟨fun n => n = some b, fun h x => by
  subst x; rcases h with h | h
  · cases h
  · exact h.symm⟩

theorem kwAt_ne (b : Bool) : kwAt b ≠ iprop(False) := fun h => by
  have : (kwAt b).p (some b) := rfl
  rw [h] at this; exact this

/-- Leaves of the KW frame. -/
def kwL : KW := ⟨fun n => n ≠ none, fun h x => by
  rcases h with h | h
  · exact absurd h x
  · exact h ▸ x⟩

/-- Non-idempotent lax modality on KW: True if R is satisfiable somewhere, else the leaves.
Intro, mono and framing hold; kwG (kwG False) = True but kwG False = kwL. -/
def kwG (R : KW) : KW := ⟨fun n => R ≠ iprop(False) ∨ n ≠ none, fun h x => x.imp id (kwL.mono h)⟩

theorem kw_ne_false {R : KW} : R ≠ iprop(False) ↔ ∃ n, R.p n := by
  refine ⟨fun h => Classical.byContradiction fun hn => h (KW.ext' fun n => ⟨fun hx => hn ⟨n, hx⟩, fun hf => hf.elim⟩),
    fun ⟨n, hn⟩ e => ?_⟩
  rw [e] at hn; exact hn

theorem kw_root {P : KW} (h : P.p none) (m : Option Bool) : P.p m := P.mono (.inl rfl) h

theorem kwG_intro {R : KW} : R ⊢ kwG R := fun n h => .inl (kw_ne_false.2 ⟨n, h⟩)
theorem kwG_mono {P Q : KW} (h : P ⊢ Q) : kwG P ⊢ kwG Q := fun _ x =>
  x.imp (fun hp => kw_ne_false.2 (let ⟨m, hm⟩ := kw_ne_false.1 hp; ⟨m, h m hm⟩)) id
theorem kwG_frame {P Q : KW} : iprop(P ∗ kwG Q) ⊢ kwG iprop(P ∗ Q) := fun n ⟨hp, hq⟩ => by
  cases n with
  | some b => exact .inr (fun e => nomatch e)
  | none =>
    rcases hq with hq | hq
    · obtain ⟨m, hm⟩ := kw_ne_false.1 hq
      exact .inl (kw_ne_false.2 ⟨m, kw_root hp m, hm⟩)
    · exact absurd rfl hq

/-- Masked version: mask M0 is the identity, mask M1 is kwG. -/
def kwF (E : Iris.Inv.Mask) (X : KW) : KW := match E with | .M0 => X | .M1 => kwG X

theorem kwF_intro {E : Iris.Inv.Mask} {P : KW} : P ⊢ kwF E P := by
  cases E
  · exact fun _ h => h
  · exact kwG_intro
theorem kwF_mono {E : Iris.Inv.Mask} {P Q : KW} (h : P ⊢ Q) : kwF E P ⊢ kwF E Q := by
  cases E
  · exact h
  · exact kwG_mono h
theorem kwF_frame {E : Iris.Inv.Mask} {P Q : KW} : iprop(P ∗ kwF E Q) ⊢ kwF E iprop(P ∗ Q) := by
  cases E
  · exact fun _ h => h
  · exact kwG_frame
/-- inv_fupd for pure invariants "X is satisfiable somewhere" with kwF. -/
theorem kwF_inv {X Q R : KW} (hp : iprop(X ∗ Q) ⊢ kwF .M0 iprop(X ∗ R)) :
    iprop(⌜X ≠ iprop(False)⌝ ∗ Q) ⊢ kwF .M1 R := fun n ⟨hX, hQ⟩ => by
  cases n with
  | some b => exact .inr (fun e => nomatch e)
  | none =>
    obtain ⟨m, hm⟩ := kw_ne_false.1 hX
    exact .inl (kw_ne_false.2 ⟨m, (hp m ⟨hm, kw_root hQ m⟩).2⟩)
theorem kwGF_root : ¬ (kwG iprop(False)).p none := fun h => h.elim (fun e => e rfl) (fun e => e rfl)
theorem kwGF_leaf : (iprop(□ kwG iprop(False)) : KW).p (some true) := ⟨trivial, .inr (fun e => nomatch e)⟩

/-- Idempotent, framing, non-monotone modality on KW: True on propositions other than False
and the leaves, the leaves on those two. -/
def kwH (R : KW) : KW := ⟨fun n => (R ≠ iprop(False) ∧ R ≠ kwL) ∨ n ≠ none, fun h x => x.imp id (kwL.mono h)⟩

theorem kwL_ne_false : kwL ≠ iprop(False) := kw_ne_false.2 ⟨some true, fun e => nomatch e⟩

theorem kw_sub_L {P : KW} (h : ¬ P.p none) : P ⊢ kwL := fun n hp => by
  cases n with
  | none => exact absurd hp h
  | some b => exact fun e => nomatch e

theorem kwH_intro {R : KW} : R ⊢ kwH R := fun n h => by
  cases n with
  | some b => exact .inr (fun e => nomatch e)
  | none =>
    refine .inl ⟨kw_ne_false.2 ⟨none, h⟩, fun e => ?_⟩
    rw [e] at h; exact h rfl

theorem kwH_trans {R : KW} : kwH (kwH R) ⊢ kwH R := fun n h => by
  cases n with
  | some b => exact .inr (fun e => nomatch e)
  | none =>
    rcases h with ⟨h1, h2⟩ | h
    · refine .inl (Classical.byContradiction fun hn => h2 (KW.ext' fun m => ⟨fun hm => ?_, fun hm => .inr hm⟩))
      rcases hm with hm | hm
      · exact absurd (by cases m <;> simp_all) hn
      · exact hm
    · exact absurd rfl h

theorem kwH_frame {P Q : KW} : iprop(P ∗ kwH Q) ⊢ kwH iprop(P ∗ Q) := fun n ⟨hp, hq⟩ => by
  cases n with
  | some b => exact .inr (fun e => nomatch e)
  | none =>
    rcases hq with ⟨hq1, hq2⟩ | hq
    · have e1 : (iprop(P ∗ Q) : KW) = Q := KW.ext' fun m => ⟨fun h => h.2, fun h => ⟨kw_root hp m, h⟩⟩
      show KW.p (kwH iprop(P ∗ Q)) none
      rw [e1]; exact .inl ⟨hq1, hq2⟩
    · exact absurd rfl hq

/-- Masked modality without intro: mask M0 is constant False, mask M1 adds the leaves. -/
def kwZ (E : Iris.Inv.Mask) (X : KW) : KW := match E with | .M0 => iprop(False) | .M1 => iprop(X ∨ kwL)

theorem kwZ_mono {E : Iris.Inv.Mask} {P Q : KW} (h : P ⊢ Q) : kwZ E P ⊢ kwZ E Q := by
  cases E
  · exact fun _ h => h
  · exact fun n x => x.imp (h n) id
theorem kwZ_trans {E : Iris.Inv.Mask} {P : KW} : kwZ E (kwZ E P) ⊢ kwZ E P := by
  cases E
  · exact fun _ h => h
  · exact fun _ x => x.elim id .inr
theorem kwZ_frame {E : Iris.Inv.Mask} {P Q : KW} : iprop(P ∗ kwZ E Q) ⊢ kwZ E iprop(P ∗ Q) := by
  cases E
  · exact fun _ h => h.2
  · exact fun _ ⟨hp, hq⟩ => hq.imp (fun hq => ⟨hp, hq⟩) id
theorem kwZ_inv {X Q R : KW} (hp : iprop(X ∗ Q) ⊢ kwZ .M0 iprop(X ∗ R)) :
    iprop(⌜X ≠ iprop(False)⌝ ∗ Q) ⊢ kwZ .M1 R := fun n ⟨hX, hQ⟩ => by
  cases n with
  | some b => exact .inr (fun e => nomatch e)
  | none =>
    obtain ⟨m, hm⟩ := kw_ne_false.1 hX
    exact (hp m ⟨hm, kw_root hQ m⟩).elim
theorem kwZF_leaf : (iprop(□ kwZ .M1 iprop(False)) : KW).p (some true) := ⟨trivial, .inr (fun e => nomatch e)⟩
theorem kwZF_root : ¬ (kwZ .M1 iprop(False)).p none := fun h => h.elim (fun h => h) (fun e => e rfl)




/-- NP: Nat under addition as a discrete UORA (unit 0, core 0, all valid, order ≤); UPred NP is affine and ownM 1 is not duplicable. -/
structure NP where v : Nat

instance : OFE NP := OFE.ofDiscrete NP
instance : OFE.Discrete NP := ⟨id⟩

instance npORA : ORA NP := ORA.ofDiscreteORAData {
  pcore := fun _ => some ⟨0⟩
  op := fun a b => ⟨a.v + b.v⟩
  Valid := fun _ => True
  Order := fun a b => a.v ≤ b.v
  assoc := by intro x y z; cases x; cases y; cases z; simp only [NP.mk.injEq]; omega
  comm := by intro x y; cases x; cases y; simp only [NP.mk.injEq]; omega
  pcore_op_left := by intro x cx h; cases h; cases x; simp
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := fun _ _ _ => trivial
  ord_trans := fun _ _ _ h1 h2 => Nat.le_trans h1 h2
  op_mono_left := by intro x y z h; show _ ≤ _; dsimp only; have : x.v ≤ y.v := h; omega
  valid_of_ord := fun _ _ _ _ => trivial
  pcore_mono := by intro x y cx h1 h2; cases h2; exact ⟨⟨0⟩, rfl, Nat.le_refl 0⟩
  pcore_order_op := by intro x cx h y; cases h; exact ⟨⟨0⟩, rfl, Nat.le_refl 0⟩
  pcore_increasing := by intro x cx h y; cases h; show _ ≤ _; dsimp only; omega
  increasing_closed := by intro x y _ _ z; show _ ≤ _; dsimp only; omega }

instance : OrderRefl NP := ⟨fun x => Nat.le_refl x.v⟩

instance npUORA : UORA NP where
  unit := ⟨0⟩
  unit_valid := trivial
  unit_left_id := by intro x; cases x; simp [Op.op]
  pcore_unit := rfl

instance : IncOrd NP := ⟨by
  intro x y ⟨z, hz⟩
  have : y = ⟨x.v + z.v⟩ := hz
  subst this; exact Nat.le_add_right _ _⟩

theorem np_pers1 : iprop(<pers> UPred.ownM (⟨1⟩ : NP)) ⊢ iprop(False) := fun _ _ h =>
  (Nat.not_succ_le_zero 0 (h : (1 : Nat) ≤ 0)).elim

/-- Non-persistent saved proposition: ownership of 1 plus "P is False". -/
def npSaved (_ : Unit) (Q : UPred NP) : UPred NP := iprop(UPred.ownM (⟨1⟩ : NP) ∧ ⌜Q ⊣⊢ iprop(False)⌝)

theorem npSaved_agree : ∀ (i : Unit) (P Q : UPred NP), iprop(npSaved i P ∧ npSaved i Q) ⊢ iprop(□ (P ↔ Q)) :=
  fun _ P Q => (and_mono and_elim_r and_elim_r).trans (pure_and.1.trans (pure_elim' fun ⟨hp, hq⟩ =>
    true_emp.1.trans (intuitionistically_emp.2.trans (intuitionistically_mono (and_intro
      (imp_intro (and_elim_r.trans (hp.1.trans false_elim)))
      (imp_intro (and_elim_r.trans (hq.1.trans false_elim))))))))

theorem npA_false : Iris.SavedProp.A (PROP := UPred NP) Unit npSaved () ⊢ iprop(False) :=
  exists_elim fun _ => affinely_elim.trans ((persistently_mono (sep_elim_right.trans and_elim_l)).trans np_pers1)




/-- Tokens: empty, start (exclusive), finished (duplicable), conflict. -/
inductive Tk where | e | s | f | bot
  deriving DecidableEq

def Tk.op : Tk → Tk → Tk
  | .e, x => x
  | x, .e => x
  | .f, .f => .f
  | _, _ => .bot

def Tk.core : Tk → Tk
  | .s => .e
  | x => x

theorem Tk.op_assoc (a b c : Tk) : a.op (b.op c) = (a.op b).op c := by
  cases a <;> cases b <;> cases c <;> rfl
theorem Tk.op_comm (a b : Tk) : a.op b = b.op a := by cases a <;> cases b <;> rfl
theorem Tk.core_op (a : Tk) : a.core.op a = a := by cases a <;> rfl
theorem Tk.core_idem (a : Tk) : a.core.core = a.core := by cases a <;> rfl
theorem Tk.core_le (a b : Tk) : a.core.op (a.op b).core = (a.op b).core := by
  cases a <;> cases b <;> rfl
theorem Tk.op_bot (a b : Tk) (h : a.op b ≠ .bot) : a ≠ .bot := by
  cases a <;> cases b <;> simp_all [Tk.op]
theorem Tk.op_e (a b : Tk) (h : a.op b = .e) : a = .e := by
  cases a <;> cases b <;> simp_all [Tk.op]

/-- TM: name-indexed token maps; valid = no conflict and finite support. -/
structure TM where g : Nat → Tk

def TM.op (x y : TM) : TM := ⟨fun n => (x.g n).op (y.g n)⟩
def TM.Valid (x : TM) : Prop := (∀ n, x.g n ≠ .bot) ∧ ∃ N, ∀ n, N ≤ n → x.g n = .e

instance : OFE TM := OFE.ofDiscrete TM
instance : OFE.Discrete TM := ⟨id⟩

theorem TM.op_assoc (x y z : TM) : x.op (y.op z) = (x.op y).op z := by
  simp only [TM.op, Tk.op_assoc]
theorem TM.op_comm (x y : TM) : x.op y = y.op x := by
  simp only [TM.op]; congr 1; funext n; exact Tk.op_comm _ _

instance tmORA : ORA TM := ORA.ofDiscreteORAData {
  pcore := fun x => some ⟨fun n => (x.g n).core⟩
  op := TM.op
  Valid := TM.Valid
  Order := fun x y => ∃ z, y = x.op z
  assoc := TM.op_assoc
  comm := TM.op_comm
  pcore_op_left := by
    intro x cx h; cases h; simp only [TM.op, Tk.core_op]
  pcore_idem := by
    intro x cx h; cases h; simp only [Tk.core_idem]
  valid_op_left := fun x y ⟨h1, N, h2⟩ =>
    ⟨fun n => Tk.op_bot _ _ (h1 n), N, fun n hn => Tk.op_e _ _ (h2 n hn)⟩
  ord_trans := by
    rintro x y z ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a.op b, (TM.op_assoc _ _ _).symm⟩
  op_mono_left := by
    rintro x y z ⟨a, rfl⟩
    exact ⟨a, by rw [← TM.op_assoc, TM.op_comm a z, TM.op_assoc]⟩
  valid_of_ord := by
    rintro x y ⟨a, rfl⟩ ⟨h1, N, h2⟩
    exact ⟨fun n => Tk.op_bot _ _ (h1 n), N, fun n hn => Tk.op_e _ _ (h2 n hn)⟩
  pcore_mono := by
    rintro x y cx ⟨a, rfl⟩ h; cases h
    exact ⟨_, rfl, ⟨⟨fun n => ((x.g n).op (a.g n)).core⟩, by simp only [TM.op, Tk.core_le]⟩⟩
  pcore_order_op := by
    intro x cx h y; cases h
    exact ⟨_, rfl, ⟨⟨fun n => ((x.g n).op (y.g n)).core⟩, by simp only [TM.op, Tk.core_le]⟩⟩
  pcore_increasing := by
    intro x cx _ y; exact ⟨cx, TM.op_comm _ _⟩
  increasing_closed := by
    intro x y _ _ z; exact ⟨y, TM.op_comm _ _⟩ }

def tmUnit : TM := ⟨fun _ => .e⟩

theorem tm_unit_op (x : TM) : tmUnit.op x = x := by cases x; rfl
theorem tm_op_unit (x : TM) : x.op tmUnit = x := by rw [TM.op_comm]; exact tm_unit_op x

instance : OrderRefl TM := ⟨fun x => ⟨tmUnit, (tm_op_unit x).symm⟩⟩

instance tmUORA : UORA TM where
  unit := tmUnit
  unit_valid := ⟨fun _ h => Tk.noConfusion h, 0, fun _ _ => rfl⟩
  unit_left_id := tm_unit_op _
  pcore_unit := rfl

instance : IncOrd TM := ⟨by rintro x y ⟨z, hz⟩; exact ⟨z, hz⟩⟩

def tok (γ : Nat) (t : Tk) : TM := ⟨fun n => if n = γ then t else .e⟩

theorem tm_cons : ¬ (⊢@{UPred TM} |==> False) := fun h => by
  obtain ⟨_, _, hf⟩ := h 0 ⟨tmUnit, ⟨fun _ h => Tk.noConfusion h, 0, fun _ _ => rfl⟩⟩
    ⟨tmUnit, (tm_unit_op tmUnit).symm⟩ 0 tmUnit (Nat.le_refl 0) ⟨fun _ h => Tk.noConfusion h, 0, fun _ _ => rfl⟩
  exact hf

theorem tm_alloc : ⊢@{UPred TM} |==> ∃ γ, UPred.ownM (tok γ .s) := by
  have upd : UpdateP (UORA.unit : TM) (fun y => ∃ γ, y = tok γ .s) := by
    intro n mz hv
    cases mz with
    | none =>
      refine ⟨tok 0 .s, ⟨0, rfl⟩, fun k => ?_, 1, fun k hk => ?_⟩
      · show (if k = 0 then Tk.s else .e) ≠ .bot
        split <;> exact fun h => Tk.noConfusion h
      · show (if k = 0 then Tk.s else .e) = .e
        rw [if_neg (by omega)]
    | some z =>
      obtain ⟨h1, N, h2⟩ := (hv : TM.Valid (tmUnit.op z))
      replace h1 : ∀ k, z.g k ≠ .bot := h1
      replace h2 : ∀ k, N ≤ k → z.g k = .e := h2
      refine ⟨tok N .s, ⟨N, rfl⟩, fun k => ?_, N + 1, fun k hk => ?_⟩
      · show (if k = N then Tk.s else .e).op (z.g k) ≠ .bot
        by_cases e : k = N
        · subst e; rw [if_pos rfl, h2 k (Nat.le_refl k)]; exact fun h => Tk.noConfusion h
        · rw [if_neg e]; exact h1 k
      · show (if k = N then Tk.s else .e).op (z.g k) = .e
        rw [if_neg (by omega)]; exact h2 k (by omega)
  refine (UPred.bupd_ownM_updateP _ _ upd).trans (BIUpdate.mono (exists_elim fun y =>
    pure_elim_left fun ⟨γ, hy⟩ => hy ▸ exists_intro (Ψ := fun γ => UPred.ownM (tok γ .s)) γ))

theorem tm_finish (γ : Nat) : UPred.ownM (tok γ .s) ⊢ |==> UPred.ownM (tok γ .f) := by
  have upd : UpdateP (tok γ .s) (fun y => y = tok γ .f) := by
    intro n mz hv
    cases mz with
    | none =>
      refine ⟨tok γ .f, rfl, fun k => ?_, γ + 1, fun k hk => ?_⟩
      · show (if k = γ then Tk.f else .e) ≠ .bot
        split <;> exact fun h => Tk.noConfusion h
      · show (if k = γ then Tk.f else .e) = .e
        rw [if_neg (by omega)]
    | some z =>
      obtain ⟨h1, N, h2⟩ := (hv : TM.Valid ((tok γ .s).op z))
      have hz : z.g γ = .e := by
        have := h1 γ
        revert this
        show (if γ = γ then Tk.s else .e).op (z.g γ) ≠ .bot → _
        rw [if_pos rfl]; cases z.g γ <;> simp [Tk.op]
      refine ⟨tok γ .f, rfl, fun k => ?_, N, fun k hk => ?_⟩
      · show (if k = γ then Tk.f else .e).op (z.g k) ≠ .bot
        by_cases e : k = γ
        · subst e; rw [if_pos rfl, hz]; exact fun h => Tk.noConfusion h
        · have := h1 k; revert this
          show (if k = γ then Tk.s else .e).op (z.g k) ≠ .bot → _
          rw [if_neg e, if_neg e]; exact id
      · have := h2 k hk; revert this
        show (if k = γ then Tk.s else .e).op (z.g k) = .e → (if k = γ then Tk.f else .e).op (z.g k) = .e
        by_cases e : k = γ
        · subst e; rw [if_pos rfl, hz]; exact fun h => Tk.noConfusion h
        · rw [if_neg e, if_neg e]; exact id
  refine (UPred.bupd_ownM_updateP _ _ upd).trans (BIUpdate.mono (exists_elim fun y =>
    pure_elim_left fun hy => hy ▸ .rfl))

theorem tm_not_start (γ : Nat) : iprop(UPred.ownM (tok γ .s) ∗ UPred.ownM (tok γ .f)) ⊢ iprop(False) :=
  (UPred.ownM_op _ _).2.trans (UPred.ownM_invalid _ fun ⟨h1, _⟩ => h1 γ (by
    show (if γ = γ then Tk.s else .e).op (if γ = γ then Tk.f else .e) = .bot
    simp [Tk.op]))

theorem tok_f_dup (γ : Nat) : (tok γ .f).op (tok γ .f) = tok γ .f := by
  simp only [TM.op, tok]; congr 1; funext n; split <;> rfl

theorem tm_dup (γ : Nat) : UPred.ownM (tok γ .f) ⊢ iprop(UPred.ownM (tok γ .f) ∗ UPred.ownM (tok γ .f)) := by
  have := (UPred.ownM_op (tok γ .f) (tok γ .f)).1
  rwa [show (tok γ .f) • (tok γ .f) = tok γ .f from tok_f_dup γ] at this

instance tm_fin_pers (γ : Nat) : Persistent (UPred.ownM (tok γ .f)) :=
  ⟨(UPred.persistently_ownM_core _).trans (persistently_mono (UPred.ownM_ord_mono
    ⟨tmUnit, by show (⟨fun n => (if n = γ then Tk.f else .e).core⟩ : TM) = (tok γ .f).op tmUnit
                rw [tm_op_unit]; simp only [tok]; congr 1; funext n; split <;> rfl⟩))⟩

/-- Owning some token. -/
def tmC : UPred TM := iprop(∃ γ, UPred.ownM (tok γ .s) ∨ UPred.ownM (tok γ .f))
/-- Mask M0 is the identity, mask M1 adds tmC. -/
def tmF (E : Iris.Inv.Mask) (X : UPred TM) : UPred TM := match E with | .M0 => X | .M1 => iprop(X ∨ tmC)

theorem Tk.l1 (a b c : Tk) (h : ((Tk.s.op a).op b).op c = .s) : b = .e := by
  cases a <;> cases b <;> cases c <;> simp_all [Tk.op]
theorem Tk.l2 (a b c : Tk) : (a.op b).op c = b.op (a.op c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem Tk.l3 (a b c d : Tk) (h : a.core = Tk.s.op d) (hv : (a.op b).op c ≠ .bot) : False := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [Tk.op, Tk.core]
theorem Tk.l4 (a b c d : Tk) (h : a.core = Tk.f.op d) (hv : (a.op b).op c ≠ .bot) : (a.op b).op c = .f := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [Tk.op, Tk.core]

/-- Owning token t at γ, for a valid map holding t at γ. -/
theorem tm_own_at {xv : Nat → Tk} {γ : Nat} {t : Tk} (h : xv γ = t) :
    ∃ z : TM, (⟨xv⟩ : TM) = (tok γ t).op z := ⟨⟨fun k => if k = γ then .e else xv k⟩, by
  simp only [TM.op, tok]; congr 1; funext k
  by_cases e : k = γ
  · subst e; rw [if_pos rfl, if_pos rfl, h]; cases t <;> rfl
  · rw [if_neg e, if_neg e]; rfl⟩

theorem tm_key_gen (γ : Nat) (X Q R : UPred TM) (hX1 : UPred.ownM (tok γ .s) ⊢ X)
    (hX2 : X ⊢ iprop(UPred.ownM (tok γ .s) ∨ □ tmF .M1 iprop(False)))
    (hp0 : iprop(X ∗ Q) ⊢ iprop(X ∗ R)) :
    Q ⊢ iprop(R ∨ tmC) := by
  have hp := (sep_mono_left hX1).trans (hp0.trans (sep_mono_left hX2))
  intro n x hQ
  obtain ⟨⟨xv⟩, hxv⟩ := x
  by_cases hx : xv γ = .e
  · have hv : ✓{n} ((tok γ .s).op ⟨xv⟩) := by
      obtain ⟨h1, N, h2⟩ := (hxv : TM.Valid ⟨xv⟩)
      refine ⟨fun k => ?_, max N (γ + 1), fun k hk => ?_⟩
      · show (if k = γ then Tk.s else .e).op (xv k) ≠ .bot
        by_cases e : k = γ
        · subst e; rw [if_pos rfl, hx]; exact fun h => Tk.noConfusion h
        · rw [if_neg e]; exact h1 k
      · show (if k = γ then Tk.s else .e).op (xv k) = .e
        rw [if_neg (by omega)]; exact h2 k (by omega)
    have hS := hp n ⟨_, hv⟩ ⟨tok γ .s, ⟨xv⟩, ⟨tmUnit, (tm_op_unit _).symm⟩,
      ⟨tmUnit, (tm_op_unit _).symm⟩, hQ⟩
    obtain ⟨y1, y2, ⟨w, hw⟩, hy1, hy2⟩ := hS
    have hk : ∀ k, (if k = γ then Tk.s else .e).op (xv k) = ((y1.g k).op (y2.g k)).op (w.g k) :=
      fun k => congrArg (fun t : TM => t.g k) (hw : (tok γ .s).op ⟨xv⟩ = (y1.op y2).op w)
    rcases hy1 with ⟨z1, hz1⟩ | ⟨_, h1⟩
    · have hz : ∀ k, y1.g k = (if k = γ then Tk.s else .e).op (z1.g k) :=
        fun k => congrArg (fun t : TM => t.g k) (hz1 : y1 = (tok γ .s).op z1)
      have hγ := hk γ
      rw [if_pos rfl, hx, hz γ, if_pos rfl] at hγ
      have he : y2.g γ = .e := Tk.l1 _ _ _ (by rw [← hγ]; rfl)
      refine .inl (R.mono hy2 ⟨⟨fun k => if k = γ then .e else (y1.g k).op (w.g k)⟩, ?_⟩ (Nat.le_refl n))
      show (⟨xv⟩ : TM) = y2.op _
      simp only [TM.op]; congr 1; funext k
      by_cases e : k = γ
      · subst e; rw [if_pos rfl, hx, he]; rfl
      · have h2 := hk k
        rw [if_neg e] at h2 ⊢; rw [show xv k = Tk.e.op (xv k) from rfl, h2]; exact Tk.l2 _ _ _
    · rcases h1 with h1 | ⟨_, ⟨γ', rfl⟩, h1 | h1⟩
      · exact h1.elim
      · obtain ⟨z, hz⟩ := h1
        have hc := congrArg (fun t : TM => t.g γ') (hz : (⟨fun k => (y1.g k).core⟩ : TM) = (tok γ' .s).op z)
        simp only [TM.op, tok] at hc
        have hb := hv.1 γ'
        rw [show ((tok γ .s).op ⟨xv⟩).g γ' = _ from hk γ'] at hb
        exact (Tk.l3 _ _ _ _ hc hb).elim
      · obtain ⟨z, hz⟩ := h1
        have hc := congrArg (fun t : TM => t.g γ') (hz : (⟨fun k => (y1.g k).core⟩ : TM) = (tok γ' .f).op z)
        simp only [TM.op, tok] at hc
        have hb := hv.1 γ'
        rw [show ((tok γ .s).op ⟨xv⟩).g γ' = _ from hk γ'] at hb
        have hf := Tk.l4 _ _ _ _ hc hb
        by_cases e : γ' = γ
        · subst e
          have h2 := hk γ'
          rw [if_pos rfl, hx, hf] at h2
          exact Tk.noConfusion h2
        · have h2 := hk γ'
          rw [if_neg e, hf] at h2
          exact .inr ⟨_, ⟨γ', rfl⟩, .inr (tm_own_at (show xv γ' = .f from h2))⟩
  · have hb : xv γ ≠ .bot := (hxv : TM.Valid ⟨xv⟩).1 γ
    cases h : xv γ with
    | e => exact absurd h hx
    | s => exact .inr ⟨_, ⟨γ, rfl⟩, .inl (tm_own_at h)⟩
    | f => exact .inr ⟨_, ⟨γ, rfl⟩, .inr (tm_own_at h)⟩
    | bot => exact absurd h hb



theorem tmC_unit (n : Nat) (v : ValidAt TM n) (hv : ∀ k, v.val.g k = .e) : ¬ tmC.holds n v := by
  rintro ⟨_, ⟨γ, rfl⟩, ⟨z, hz⟩ | ⟨z, hz⟩⟩
  · have h3 : Tk.e = (if γ = γ then Tk.s else Tk.e).op (z.g γ) :=
      (hv γ).symm.trans (congrArg (fun t : TM => t.g γ) hz)
    rw [if_pos rfl] at h3
    cases h : z.g γ <;> rw [h] at h3 <;> exact Tk.noConfusion h3
  · have h3 : Tk.e = (if γ = γ then Tk.f else Tk.e).op (z.g γ) :=
      (hv γ).symm.trans (congrArg (fun t : TM => t.g γ) hz)
    rw [if_pos rfl] at h3
    cases h : z.g γ <;> rw [h] at h3 <;> exact Tk.noConfusion h3

theorem tm_key (γ : Nat) (Q R : UPred TM)
    (hp : iprop((UPred.ownM (tok γ .s) ∨ □ tmF .M1 iprop(False)) ∗ Q) ⊢
      iprop((UPred.ownM (tok γ .s) ∨ □ tmF .M1 iprop(False)) ∗ R)) :
    Q ⊢ iprop(R ∨ tmC) := tm_key_gen γ _ Q R or_intro_l .rfl hp

/-- The pure invariant used with tmF. -/
def tmInv (X : UPred TM) : Prop := ∀ Q R : UPred TM, (iprop(X ∗ Q) ⊢ iprop(X ∗ R)) → Q ⊢ iprop(R ∨ tmC)

theorem tmF_intro {E : Iris.Inv.Mask} {P : UPred TM} : P ⊢ tmF E P := by
  cases E
  · exact .rfl
  · exact or_intro_l
theorem tmF_mono {E : Iris.Inv.Mask} {P Q : UPred TM} (h : P ⊢ Q) : tmF E P ⊢ tmF E Q := by
  cases E
  · exact h
  · exact or_elim (h.trans or_intro_l) or_intro_r
theorem tmF_trans {E : Iris.Inv.Mask} {P : UPred TM} : tmF E (tmF E P) ⊢ tmF E P := by
  cases E
  · exact .rfl
  · exact or_elim .rfl or_intro_r
theorem tmF_frame {E : Iris.Inv.Mask} {P Q : UPred TM} : iprop(P ∗ tmF E Q) ⊢ tmF E iprop(P ∗ Q) := by
  cases E
  · exact .rfl
  · exact sep_or_left.1.trans (or_elim or_intro_l (sep_elim_right.trans or_intro_r))
theorem tmF_inv {P Q R : UPred TM} (hp : iprop(P ∗ Q) ⊢ tmF .M0 iprop(P ∗ R)) :
    iprop(⌜tmInv P⌝ ∗ Q) ⊢ tmF .M1 R :=
  (sep_mono_left (pure_elim' fun hφ => wand_intro (sep_elim_right.trans (hφ Q R hp)))).trans wand_elim_left
theorem tm_ss (γ : Nat) : iprop(UPred.ownM (tok γ .s) ∗ UPred.ownM (tok γ .s)) ⊢ iprop(False) :=
  (UPred.ownM_op _ _).2.trans (UPred.ownM_invalid _ fun ⟨h1, _⟩ => h1 γ (by
    show (if γ = γ then Tk.s else .e).op (if γ = γ then Tk.s else .e) = .bot
    simp [Tk.op]))

/-- The saved-proposition body for start = finished = the start token is equivalent to the token. -/
theorem tm_key_saved (γ : Nat) (P : UPred TM) :
    tmInv iprop(UPred.ownM (tok γ .s) ∨ UPred.ownM (tok γ .s) ∗ □ P) := fun Q R hp =>
  tm_key_gen γ _ Q R or_intro_l (or_elim or_intro_l (sep_elim_left.trans or_intro_l)) hp




/-- GB: Boolean non-affine BI over Bool with xor (copied from W5c2). -/

def GB := Bool → Prop

instance : BIBase GB where
  Entails P Q      := ∀ x, P x → Q x
  emp            x := x = false
  pure φ         _ := φ
  and P Q        x := P x ∧ Q x
  or P Q         x := P x ∨ Q x
  imp P Q        x := P x → Q x
  sForall Ψ      x := ∀ p, Ψ p → p x
  sExists Ψ      x := ∃ p, Ψ p ∧ p x
  sep P Q        x := ∃ a b, x = xor a b ∧ P a ∧ Q b
  wand P Q       x := ∀ y, P y → Q (xor x y)
  persistently P _ := P false
  later P        x := P x

instance : COFE GB := COFE.ofDiscrete _

instance gbBI : BI GB where
  entails_refl _ h := h
  entails_trans h1 h2 x h := h2 x (h1 x h)
  equiv_iff {P Q} := ⟨fun h => h ▸ ⟨fun _ h => h, fun _ h => h⟩,
    fun ⟨h₁, h₂⟩ => funext fun σ => propext ⟨h₁ σ, h₂ σ⟩⟩
  and_ne          := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  or_ne           := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  imp_ne          := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  sep_ne          := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  wand_ne         := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  persistently_ne := ⟨by rintro _ _ _ h; exact (h : _ = _) ▸ rfl⟩
  later_ne        := ⟨by rintro _ _ _ h; exact (h : _ = _) ▸ rfl⟩
  sForall_ne {_ P Q} h := (liftRel_eq.1 (h : liftRel Eq P Q)) ▸ rfl
  sExists_ne {_ P Q} h := (liftRel_eq.1 (h : liftRel Eq P Q)) ▸ rfl
  pure_intro h _ _ := h
  pure_elim' h σ hφ := h hφ σ ⟨⟩
  and_elim_l _ h := h.1
  and_elim_r _ h := h.2
  and_intro h1 h2 x h := ⟨h1 x h, h2 x h⟩
  or_intro_l _ h := .inl h
  or_intro_r _ h := .inr h
  or_elim h1 h2 x h := h.elim (h1 x) (h2 x)
  imp_intro h x hP hQ := h x ⟨hP, hQ⟩
  imp_elim h x hPQ := h x hPQ.1 hPQ.2
  sForall_intro h x hP p hp := h p hp x hP
  sForall_elim hp _ h := h _ hp
  sExists_intro hp _ h := ⟨_, hp, h⟩
  sExists_elim h x := fun ⟨p, hp, hx⟩ => h p hp x hx
  sep_mono h1 h2 _ := fun ⟨a, b, e, ha, hb⟩ => ⟨a, b, e, h1 a ha, h2 b hb⟩
  emp_sep := ⟨fun _ ⟨a, b, e, ha, hb⟩ => by
      have ha' : a = false := ha
      subst ha'; subst e; simpa using hb,
    fun x h => ⟨false, x, by simp, rfl, h⟩⟩
  sep_symm _ := fun ⟨a, b, e, ha, hb⟩ => ⟨b, a, by subst e; cases a <;> cases b <;> rfl, hb, ha⟩
  sep_assoc_l _ := fun ⟨ab, c, e, ⟨a, b, e2, ha, hb⟩, hc⟩ =>
    ⟨a, xor b c, by subst e; subst e2; cases a <;> cases b <;> cases c <;> rfl, ha, b, c, rfl, hb, hc⟩
  wand_intro h x hP y hQ := h (xor x y) ⟨x, y, rfl, hP, hQ⟩
  wand_elim h _ := fun ⟨a, b, e, ha, hb⟩ => e ▸ h a ha b hb
  persistently_mono h _ hP := h false hP
  persistently_idem_2 _ h := h
  persistently_emp_2 _ _ := (rfl : false = false)
  persistently_and_2 _ h := h
  persistently_absorb_l _ := fun ⟨_, _, _, ha, _⟩ => ha
  persistently_and_l x h := ⟨false, x, by cases x <;> rfl, h.1, h.2⟩
  later_mono h := h
  later_intro _ h := h
  later_sForall_2 _ h _ hp := h _ ⟨_, rfl⟩ hp
  later_sExists_false _ := fun ⟨p, hp⟩ => .inr ⟨_, ⟨_, rfl⟩, hp⟩
  later_sep := ⟨fun _ h => h, fun _ h => h⟩
  later_persistently := ⟨fun _ h => h, fun _ h => h⟩
  later_false_em _ h := .inr fun _ => h

def own1 : GB := fun x => x = true

theorem gb_true_pers : Persistent (iprop(True) : GB) := ⟨fun _ _ => trivial⟩
theorem gb_true_dup : (iprop(True) : GB) ⊢ iprop(True ∗ True) := fun x _ => ⟨x, false, by cases x <;> rfl, trivial, trivial⟩
theorem gb_emp_true : ¬ (iprop(emp) : GB) true := fun h => Bool.noConfusion (h : true = false)




/-- Constant-True fancy update on SiProp (copied from W8c0): lawful, all mask laws trivial. -/
@[reducible] def topFupd : BIFUpdate SiProp where
  fupd _ _ _ := iprop(True)
  ne := ⟨fun _ _ _ _ _ _ => Iff.rfl⟩
  subset _ := fun _ _ => trivial
  except0 := fun _ _ => trivial
  mono _ := fun _ h => h
  trans := fun _ h => h
  mask_frame_right_strong _ := fun _ h => h
  frame_right := fun _ _ => trivial

end T1c2

open Iris Iris.BI T1c2

-- `Iris.Inv.contradiction` idx 11: removable (mask_mono derived: inv_alloc True framed into fupd M1, then inv_fupd with P = True turns fupd M0 X into fupd M1 X, fupd_fupd)
theorem t1c2_1 : drop% Iris.Inv.contradiction 11 := by
  intro PROP _ _ fupd name inv _ hi hm hff hfl hia hif hc gname start finished sa sf fns fd
  refine Iris.Inv.contradiction fupd name inv hi hm hff hfl ?_ hia hif hc gname start finished sa sf fns fd
  intro X
  exact sep_emp.2.trans ((sep_mono_right (true_intro.trans (hia iprop(True)))).trans
    ((hfl).trans ((hm (sep_comm.1.trans <| sep_exists_right.1.trans (exists_elim fun i =>
      hif (i := i) iprop(True) (fupd .M0 X) X hfl))).trans hff)))

-- `Iris.Inv.contradiction'` idx 11: removable (mask_mono derived: inv_alloc True framed into fupd M1, then inv_fupd with P = True turns fupd M0 X into fupd M1 X, fupd_fupd)
theorem t1c2_2 : drop% Iris.Inv.contradiction' 11 := by
  intro PROP _ _ fupd name inv _ hi hm hff hfl hia hif hc gname start finished _ sa sf fns
  refine Iris.Inv.contradiction' fupd name inv hi hm hff hfl ?_ hia hif hc start finished sa sf fns
  intro X
  exact sep_emp.2.trans ((sep_mono_right (true_intro.trans (hia iprop(True)))).trans
    ((hfl).trans ((hm (sep_comm.1.trans <| sep_exists_right.1.trans (exists_elim fun i =>
      hif (i := i) iprop(True) (fupd .M0 X) X hfl))).trans hff)))

-- `Iris.SavedProp.saved_A` idx 7: necessary (KW branching Kripke BI (root below two leaves), saved i Q = pure (Q ≠ False): A holds at a leaf via P = the other leaf, not at the root)
theorem t1c2_3 : ¬ drop0% Iris.SavedProp.saved_A 7 := fun h => by
  have H := @h KW _ _ _ Unit (fun _ Q => iprop(⌜Q ≠ iprop(False)⌝)) (fun _ _ => kwPers _) () none
  have hA : Iris.SavedProp.A (PROP := KW) Unit (fun _ Q => iprop(⌜Q ≠ iprop(False)⌝)) () ≠ iprop(False) := fun e => by
    have : KW.p (Iris.SavedProp.A (PROP := KW) Unit (fun _ Q => iprop(⌜Q ≠ iprop(False)⌝)) ()) (some true) :=
      ⟨_, ⟨kwAt false, rfl⟩, trivial, fun m hm hb => by
        rcases hm with hm | hm
        · cases hm
        · subst hm; exact Bool.noConfusion (Option.some.inj hb), kwAt_ne false⟩
    rw [e] at this; exact this
  obtain ⟨_, ⟨P, rfl⟩, _, hnP, hP⟩ := H hA
  apply hP
  apply KW.ext'
  intro n
  refine ⟨fun hp => hnP n (.inl rfl) hp, fun hf => hf.elim⟩

-- `Iris.SavedProp.saved_A` idx 6: necessary (UPred NP, saved i Q = ownM 1 ∧ pure (Q ⊣⊢ False): agreement holds, A ⊢ <pers> ownM 1 ⊢ False, saved i (A i) holds at resource 1)
theorem t1c2_4 : ¬ drop0% Iris.SavedProp.saved_A 6 := fun h => by
  have H := @h (UPred NP) _ _ _ Unit npSaved npSaved_agree ()
  exact (H.trans npA_false) 0 ⟨⟨1⟩, trivial⟩ ⟨Nat.le_refl 1, ⟨npA_false, false_elim⟩⟩

-- `Iris.Linear.leak` idx 11: removable (frame not needed: ▷True is absorbing, so ▷True ∗ cinv_own ⊢ ▷True feeds the closing wand directly; P ⊢ True ⊢ ▷True, cinv_alloc, cinv_acc, fupd_mono, fupd_fupd twice)
theorem t1c2_9 : drop% Iris.Linear.leak 11 := by
  intro M1 M0 PROP _ P fupd gname cinv own hm hff halloc hacc
  have acc : ∀ γ, iprop(cinv γ iprop(True) ∗ own γ) ⊢
      fupd M1 M0 iprop(▷ True ∗ own γ ∗ (▷ True -∗ fupd M0 M1 emp)) := fun γ =>
    emp_sep.2.trans ((sep_mono_left (hacc iprop(True) γ)).trans
      (sep_assoc.2.trans ((sep_mono_left wand_elim_left).trans wand_elim_left)))
  have close : ∀ γ, iprop(▷ True ∗ own γ ∗ (▷ True -∗ fupd M0 M1 emp)) ⊢ fupd M0 M1 emp := fun γ =>
    sep_assoc.2.trans ((sep_mono_left sep_elim_left).trans wand_elim_right)
  exact true_intro.trans (later_intro.trans ((halloc (E := M1) iprop(True)).trans
    ((hm (exists_elim fun γ => (acc γ).trans (hm (close γ)))).trans (hff.trans hff))))

-- `Iris.Inv.contradiction` idx 7: removable (fupd_intro derived: X ⊢ X ∗ fupd M0 (∃ γ, start γ) (sts_alloc), frame, mono with affinity gives fupd M0 X; mask_mono gives M1)
theorem t1c2_10 : drop% Iris.Inv.contradiction 7 := by
  intro PROP _ _ fupd name inv _ hm hff hfl hmm hia hif hc gname start finished sa sf fns fd
  have h0 : ∀ {X : PROP}, X ⊢ fupd .M0 X := fun {X} =>
    sep_emp.2.trans ((sep_mono_right sa).trans (hfl.trans (hm sep_elim_left)))
  refine Iris.Inv.contradiction fupd name inv ?_ hm hff hfl hmm hia hif hc gname start finished sa sf fns fd
  intro E X; cases E
  · exact h0
  · exact h0.trans hmm

-- `Iris.Inv.contradiction'` idx 7: removable (fupd_intro derived: X ⊢ X ∗ fupd M0 (∃ γ, start γ) (sts_alloc), frame, mono with affinity gives fupd M0 X; mask_mono gives M1)
theorem t1c2_11 : drop% Iris.Inv.contradiction' 7 := by
  intro PROP _ _ fupd name inv _ hm hff hfl hmm hia hif hc gname start finished _ sa sf fns
  have h0 : ∀ {X : PROP}, X ⊢ fupd .M0 X := fun {X} =>
    sep_emp.2.trans ((sep_mono_right sa).trans (hfl.trans (hm sep_elim_left)))
  refine Iris.Inv.contradiction' fupd name inv ?_ hm hff hfl hmm hia hif hc start finished sa sf fns
  intro E X; cases E
  · exact h0
  · exact h0.trans hmm

-- `Iris.Inv.contradiction` idx 12: necessary (UPred TM (name-indexed exclusive start / duplicable finished tokens, finite support), fupd = bupd for both masks, inv = False)
theorem t1c2_5 : ¬ drop0% Iris.Inv.contradiction 12 := fun h =>
  @h (UPred TM) _ _ (fun _ X => iprop(|==> X)) Unit (fun _ _ => iprop(False)) (fun _ _ => inferInstance)
    BIUpdate.intro BIUpdate.mono BIUpdate.trans bupd_frame_left .rfl
    (fun _ _ _ _ => sep_elim_left.trans false_elim) tm_cons Nat
    (fun γ => UPred.ownM (tok γ .s)) (fun γ => UPred.ownM (tok γ .f)) tm_alloc tm_finish tm_not_start tm_dup

-- `Iris.Inv.contradiction` idx 13: necessary (UPred TM, fupd = bupd, inv = True (inv_alloc trivial))
theorem t1c2_6 : ¬ drop0% Iris.Inv.contradiction 13 := fun h =>
  @h (UPred TM) _ _ (fun _ X => iprop(|==> X)) Unit (fun _ _ => iprop(True)) (fun _ _ => inferInstance)
    BIUpdate.intro BIUpdate.mono BIUpdate.trans bupd_frame_left .rfl
    (fun _ => true_intro.trans ((exists_intro (Ψ := fun _ : Unit => iprop(True)) ()).trans BIUpdate.intro))
    tm_cons Nat
    (fun γ => UPred.ownM (tok γ .s)) (fun γ => UPred.ownM (tok γ .f)) tm_alloc tm_finish tm_not_start tm_dup

-- `Iris.Inv.contradiction'` idx 12: necessary (UPred TM, fupd = bupd, inv = False; finished tokens persistent)
theorem t1c2_7 : ¬ drop0% Iris.Inv.contradiction' 12 := fun h =>
  @h (UPred TM) _ _ (fun _ X => iprop(|==> X)) Unit (fun _ _ => iprop(False)) (fun _ _ => inferInstance)
    BIUpdate.intro BIUpdate.mono BIUpdate.trans bupd_frame_left .rfl
    (fun _ _ _ _ => sep_elim_left.trans false_elim) tm_cons Nat
    (fun γ => UPred.ownM (tok γ .s)) (fun γ => UPred.ownM (tok γ .f)) tm_fin_pers tm_alloc tm_finish tm_not_start

-- `Iris.Inv.contradiction'` idx 13: necessary (UPred TM, fupd = bupd, inv = True; finished tokens persistent)
theorem t1c2_8 : ¬ drop0% Iris.Inv.contradiction' 13 := fun h =>
  @h (UPred TM) _ _ (fun _ X => iprop(|==> X)) Unit (fun _ _ => iprop(True)) (fun _ _ => inferInstance)
    BIUpdate.intro BIUpdate.mono BIUpdate.trans bupd_frame_left .rfl
    (fun _ => true_intro.trans ((exists_intro (Ψ := fun _ : Unit => iprop(True)) ()).trans BIUpdate.intro))
    tm_cons Nat
    (fun γ => UPred.ownM (tok γ .s)) (fun γ => UPred.ownM (tok γ .f)) tm_fin_pers tm_alloc tm_finish tm_not_start

-- `Iris.Inv.contradiction` idx 6: necessary (UPred TM, fupd = bupd, linear invariants inv i P = P (inv_alloc by intro, inv_fupd by mono and affinity))
theorem t1c2_12 : ¬ drop0% Iris.Inv.contradiction 6 := fun h =>
  @h (UPred TM) _ _ (fun _ X => iprop(|==> X)) Unit (fun _ P => P)
    BIUpdate.intro BIUpdate.mono BIUpdate.trans bupd_frame_left .rfl
    (fun P => (exists_intro (Ψ := fun _ : Unit => P) ()).trans BIUpdate.intro)
    (fun _ _ _ hp => hp.trans (BIUpdate.mono sep_elim_right)) tm_cons Nat
    (fun γ => UPred.ownM (tok γ .s)) (fun γ => UPred.ownM (tok γ .f)) tm_alloc tm_finish tm_not_start tm_dup

-- `Iris.Inv.contradiction'` idx 6: necessary (UPred TM, fupd = bupd, linear invariants inv i P = P)
theorem t1c2_13 : ¬ drop0% Iris.Inv.contradiction' 6 := fun h =>
  @h (UPred TM) _ _ (fun _ X => iprop(|==> X)) Unit (fun _ P => P)
    BIUpdate.intro BIUpdate.mono BIUpdate.trans bupd_frame_left .rfl
    (fun P => (exists_intro (Ψ := fun _ : Unit => P) ()).trans BIUpdate.intro)
    (fun _ _ _ hp => hp.trans (BIUpdate.mono sep_elim_right)) tm_cons Nat
    (fun γ => UPred.ownM (tok γ .s)) (fun γ => UPred.ownM (tok γ .f)) tm_fin_pers tm_alloc tm_finish tm_not_start

-- `Iris.Inv.invariant_contradiction` idx 6: necessary (UPred TM, fupd = bupd, inv i P = P: start γ ⊢ B ⊢ |==> False, with allocation ⊢ |==> False, impossible)
theorem t1c2_14 : ¬ drop0% Iris.Inv.invariant_contradiction 6 := fun h => by
  have H := @h (UPred TM) _ _ (fun _ X => iprop(|==> X)) Unit (fun _ P => P)
    BIUpdate.intro BIUpdate.mono BIUpdate.trans bupd_frame_left
    (fun _ _ _ hp => hp.trans (BIUpdate.mono sep_elim_right)) Nat
    (fun γ => UPred.ownM (tok γ .s)) (fun γ => UPred.ownM (tok γ .f)) tm_fin_pers tm_finish tm_not_start
  exact tm_cons (tm_alloc.trans ((BIUpdate.mono (exists_elim fun γ =>
    (or_intro_l.trans (H (γ := γ) (i := ()))).trans intuitionistically_elim)).trans BIUpdate.trans))

-- `Iris.Inv.saved_NA` idx 6: necessary (UPred TM, fupd = bupd, inv i P = P: start γ gives saved γ (A γ) and A γ (via P = False), so |==> False; with allocation impossible)
theorem t1c2_15 : ¬ drop0% Iris.Inv.saved_NA 6 := fun h => by
  have H := @h (UPred TM) _ _ (fun _ X => iprop(|==> X)) Unit (fun _ P => P)
    BIUpdate.intro BIUpdate.mono BIUpdate.trans bupd_frame_left
    (fun _ _ _ hp => hp.trans (BIUpdate.mono sep_elim_right)) Nat
    (fun γ => UPred.ownM (tok γ .s)) (fun γ => UPred.ownM (tok γ .f)) tm_finish tm_not_start tm_dup
  refine tm_cons (tm_alloc.trans ((BIUpdate.mono (exists_elim fun γ => ?_)).trans BIUpdate.trans))
  have hS : ∀ X : UPred TM, UPred.ownM (tok γ .s) ⊢ iprop(∃ _ : Unit,
      UPred.ownM (tok γ .s) ∨ UPred.ownM (tok γ .f) ∗ □ X) := fun X =>
    or_intro_l.trans (exists_intro (Ψ := fun _ : Unit => iprop(UPred.ownM (tok γ .s) ∨ UPred.ownM (tok γ .f) ∗ □ X)) ())
  have nf : iprop(emp) ⊢@{UPred TM} iprop(□ (False -∗ |==> False)) :=
    intuitionistically_emp.2.trans (intuitionistically_mono (wand_intro (sep_elim_right.trans false_elim)))
  have hA := emp_sep.2.trans ((sep_mono nf (hS iprop(False))).trans
    (exists_intro (Ψ := fun P => iprop(□ (P -∗ |==> False) ∗ ∃ _ : Unit,
      UPred.ownM (tok γ .s) ∨ UPred.ownM (tok γ .f) ∗ □ P)) iprop(False)))
  exact (and_intro ((hS _).trans (H γ)) hA).trans (persistent_and_sep_mp.trans
    ((sep_mono_left intuitionistically_elim).trans wand_elim_left))

-- `Iris.SavedProp.contradiction` idx 7: removable (persistence of saved not needed: with A' i := ∃ Q, ¬Q ∧ saved i Q (∧ instead of □(¬Q ∗ saved i Q)) agreement gives saved i (A' i) ∧ A' i ⊢ False and saved i (A' i) ⊢ A' i by ∧-duplication; sprop_alloc_dep with A', bupd_mono gives ⊢ bupd False)
theorem t1c2_16 : drop% Iris.SavedProp.contradiction 7 := by
  intro PROP _ _ _ bupd ident saved hi hm ht hf halloc hag hc
  apply hc
  let A' : ident → PROP := fun i => iprop(∃ Q, ¬Q ∧ saved i Q)
  have hNA : ∀ i, iprop(saved i (A' i) ∧ A' i) ⊢ iprop(False) := fun i => by
    refine and_exists_left.1.trans (exists_elim fun Q => ?_)
    have h1 : iprop(saved i (A' i) ∧ (¬Q ∧ saved i Q)) ⊢ iprop(¬Q) := and_elim_r.trans and_elim_l
    have h2 : iprop(saved i (A' i) ∧ (¬Q ∧ saved i Q)) ⊢ A' i :=
      and_elim_r.trans (exists_intro (Ψ := fun Q => iprop(¬Q ∧ saved i Q)) Q)
    have h3 : iprop(saved i (A' i) ∧ (¬Q ∧ saved i Q)) ⊢ iprop(□ (Q ↔ A' i)) := (and_intro (and_elim_r.trans and_elim_r) and_elim_l).trans (hag i Q (A' i))
    have h4 := (and_intro (h3.trans (intuitionistically_elim.trans and_elim_r)) h2).trans imp_elim_left
    exact (and_intro h1 h4).trans imp_elim_left
  have hS : ∀ i, saved i (A' i) ⊢ A' i := fun i =>
    (and_intro (imp_intro (hNA i)) .rfl).trans (exists_intro (Ψ := fun Q => iprop(¬Q ∧ saved i Q)) (A' i))
  exact halloc.trans (hm (exists_elim fun i => (and_intro .rfl (hS i)).trans (hNA i)))

-- `Iris.Inv.saved_A` idx 11: necessary (KW, fupd = id, inv i X = pure (X ≠ False), start = False, finished = True: saved γ P holds iff P is satisfiable somewhere; A holds at a leaf (P = the other leaf) but not at the root)
theorem t1c2_17 : ¬ drop0% Iris.Inv.saved_A 11 := fun h => by
  have H := @h KW _ _ (fun _ X => X) Unit (fun _ X => iprop(⌜X ≠ iprop(False)⌝)) (fun _ _ => kwPers _)
    (fun _ h => h) (fun h => h) (fun _ h => h) (fun _ h => h) Unit (fun _ => iprop(False)) (fun _ => iprop(True))
    (fun _ _ _ => trivial) (fun _ _ h => h.1) (fun _ _ h => ⟨h, h⟩) ()
  have key : ∀ P : KW, (iprop(iprop(False) ∨ iprop(True) ∗ □ P) : KW) ≠ iprop(False) → ∃ n, P.p n := by
    intro P hP
    refine Classical.byContradiction fun hn => hP (KW.ext' fun n => ⟨fun hx => ?_, fun hf => hf.elim⟩)
    rcases hx with hx | ⟨_, hx⟩
    · exact hx
    · exact hn ⟨n, hx.2⟩
  have nz : ∀ P : KW, (∃ n, P.p n) → (iprop(iprop(False) ∨ iprop(True) ∗ □ P) : KW) ≠ iprop(False) := by
    intro P ⟨n, hn⟩ e
    have : KW.p (iprop(iprop(False) ∨ iprop(True) ∗ □ P) : KW) n := .inr ⟨trivial, trivial, hn⟩
    rw [e] at this; exact this
  obtain ⟨_, ⟨P, rfl⟩, hnP, _, ⟨_, rfl⟩, hsP⟩ := H none ⟨_, ⟨(), rfl⟩, nz _ ⟨some true,
    ⟨_, ⟨kwAt false, rfl⟩, ⟨trivial, fun m hm hb => by
        rcases hm with hm | hm
        · cases hm
        · subst hm; exact Bool.noConfusion (Option.some.inj hb)⟩,
      ⟨_, ⟨(), rfl⟩, nz _ ⟨some false, rfl⟩⟩⟩⟩⟩
  obtain ⟨n, hn⟩ := key P hsP
  exact hnP.2 n (.inl rfl) hn

-- `Iris.Inv.contradiction` idx 9: necessary (KW with kwG (True on satisfiable propositions, the leaves on False: intro, mono, framing, not idempotent), fupd = kwG for both masks, inv i X = pure (X valid), start/finished = the two leaves; consistency since kwG False = leaves)
theorem t1c2_18 : ¬ drop0% Iris.Inv.contradiction 9 := fun h =>
  @h KW _ _ (fun _ X => kwG X) Unit (fun _ X => iprop(⌜X.p none⌝)) (fun _ _ => kwPers _)
    kwG_intro kwG_mono kwG_frame (fun _ h => h)
    (fun P n hp => by
      cases n with
      | some b => exact .inr (fun e => nomatch e)
      | none => exact .inl (kw_ne_false.2 ⟨none, ⟨_, ⟨(), rfl⟩, hp⟩⟩))
    (fun X Q R hp n ⟨hX, hQ⟩ => by
      cases n with
      | some b => exact .inr (fun e => nomatch e)
      | none =>
        rcases hp none ⟨hX, hQ⟩ with h1 | h1
        · obtain ⟨m, _, hm⟩ := kw_ne_false.1 h1
          exact .inl (kw_ne_false.2 ⟨m, hm⟩)
        · exact absurd rfl h1)
    (fun h' => (h' none trivial).elim (fun e => e rfl) (fun e => e rfl))
    Unit (fun _ => kwAt true) (fun _ => kwAt false)
    (fun _ _ => .inl (kw_ne_false.2 ⟨some true, ⟨_, ⟨(), rfl⟩, rfl⟩⟩))
    (fun _ _ _ => .inl (kwAt_ne false))
    (fun _ _ ⟨h1, h2⟩ => Bool.noConfusion (Option.some.inj (h1.symm.trans h2)))
    (fun _ _ h => ⟨h, h⟩)

-- `Iris.Inv.contradiction'` idx 9: necessary (KW with kwG (True on satisfiable propositions, the leaves on False: intro, mono, framing, not idempotent), fupd = kwG for both masks, inv i X = pure (X valid), start/finished = the two leaves)
theorem t1c2_19 : ¬ drop0% Iris.Inv.contradiction' 9 := fun h =>
  @h KW _ _ (fun _ X => kwG X) Unit (fun _ X => iprop(⌜X.p none⌝)) (fun _ _ => kwPers _)
    kwG_intro kwG_mono kwG_frame (fun _ h => h)
    (fun P n hp => by
      cases n with
      | some b => exact .inr (fun e => nomatch e)
      | none => exact .inl (kw_ne_false.2 ⟨none, ⟨_, ⟨(), rfl⟩, hp⟩⟩))
    (fun X Q R hp n ⟨hX, hQ⟩ => by
      cases n with
      | some b => exact .inr (fun e => nomatch e)
      | none =>
        rcases hp none ⟨hX, hQ⟩ with h1 | h1
        · obtain ⟨m, _, hm⟩ := kw_ne_false.1 h1
          exact .inl (kw_ne_false.2 ⟨m, hm⟩)
        · exact absurd rfl h1)
    (fun h' => (h' none trivial).elim (fun e => e rfl) (fun e => e rfl))
    Unit (fun _ => kwAt true) (fun _ => kwAt false) (fun _ => kwPers _)
    (fun _ _ => .inl (kw_ne_false.2 ⟨some true, ⟨_, ⟨(), rfl⟩, rfl⟩⟩))
    (fun _ _ _ => .inl (kwAt_ne false))
    (fun _ _ ⟨h1, h2⟩ => Bool.noConfusion (Option.some.inj (h1.symm.trans h2)))

-- `Iris.Inv.invariant_contradiction` idx 9: necessary (KW, fupd M0 = id, fupd M1 = kwG (not idempotent), inv i X = pure (X ≠ False), start = False, finished = True: I holds (□ kwG False = leaves is satisfiable), B fails at the root)
theorem t1c2_20 : ¬ drop0% Iris.Inv.invariant_contradiction 9 := fun h => by
  have H := @h KW _ _ kwF Unit (fun _ X => iprop(⌜X ≠ iprop(False)⌝)) (fun _ _ => kwPers _)
    kwF_intro kwF_mono kwF_frame (fun _ _ _ hp => kwF_inv hp) Unit (fun _ => iprop(False)) (fun _ => iprop(True))
    (fun _ => kwPers _) (fun _ _ _ => trivial) (fun _ _ h => h.1)
  exact kwGF_root (H (γ := ()) (i := ()) none (kw_ne_false.2 ⟨some true, .inr kwGF_leaf⟩)).2

-- `Iris.Inv.finished_contradiction` idx 8: necessary (KW, fupd M0 = id, fupd M1 = kwG (not idempotent), inv i X = pure (X ≠ False), start = False, finished = True: finished ∗ I holds at the root, B fails there)
theorem t1c2_21 : ¬ drop0% Iris.Inv.finished_contradiction 8 := fun h => by
  have H := @h KW _ _ kwF Unit (fun _ X => iprop(⌜X ≠ iprop(False)⌝)) (fun _ _ => kwPers _)
    kwF_intro (fun _ _ _ hp => kwF_inv hp) Unit (fun _ => iprop(False)) (fun _ => iprop(True))
    (fun _ => kwPers _) (fun _ _ h => h.1) () ()
  exact kwGF_root (H none ⟨trivial, kw_ne_false.2 ⟨some true, .inr kwGF_leaf⟩⟩).2

-- `Iris.Inv.saved_NA` idx 9: necessary (KW, fupd M0 = id, fupd M1 = kwG (not idempotent), inv i X = pure (X ≠ False), start = False, finished = True: A holds at the root (P = a leaf), so saved (A) holds, but □(A -∗ kwG False) fails at the root)
theorem t1c2_22 : ¬ drop0% Iris.Inv.saved_NA 9 := fun h => by
  have H := @h KW _ _ kwF Unit (fun _ X => iprop(⌜X ≠ iprop(False)⌝)) (fun _ _ => kwPers _)
    kwF_intro kwF_mono kwF_frame (fun _ _ _ hp => kwF_inv hp) Unit (fun _ => iprop(False)) (fun _ => iprop(True))
    (fun _ _ _ => trivial) (fun _ _ h => h.1) (fun _ _ h => ⟨h, h⟩) ()
  have hA : KW.p (Iris.Inv.A kwF Unit (fun _ X => iprop(⌜X ≠ iprop(False)⌝)) Unit
      (fun _ => iprop(False)) (fun _ => iprop(True)) ()) none :=
    ⟨_, ⟨kwAt true, rfl⟩, ⟨trivial, fun m _ hm => .inr (by rw [show m = some true from hm]; exact fun e => nomatch e)⟩,
      ⟨_, ⟨(), rfl⟩, kw_ne_false.2 ⟨some true, .inr ⟨trivial, trivial, rfl⟩⟩⟩⟩
  exact kwGF_root ((H none ⟨_, ⟨(), rfl⟩, kw_ne_false.2 ⟨none, .inr ⟨trivial, trivial, hA⟩⟩⟩).2 none (.inl rfl) hA)

-- `Iris.Inv.contradiction` idx 8: necessary (KW with kwH (True except on False and the leaves, which go to the leaves: intro, idempotent, framing, not monotone), fupd = kwH for both masks, inv i X = pure (X valid), start/finished = the two leaves)
theorem t1c2_23 : ¬ drop0% Iris.Inv.contradiction 8 := fun h =>
  @h KW _ _ (fun _ X => kwH X) Unit (fun _ X => iprop(⌜X.p none⌝)) (fun _ _ => kwPers _)
    kwH_intro kwH_trans kwH_frame (fun _ h => h)
    (fun P n hp => by
      cases n with
      | some b => exact .inr (fun e => nomatch e)
      | none =>
        refine .inl ⟨kw_ne_false.2 ⟨none, ⟨_, ⟨(), rfl⟩, hp⟩⟩, fun e => ?_⟩
        have : KW.p (iprop(∃ _ : Unit, ⌜P.p none⌝) : KW) none := ⟨_, ⟨(), rfl⟩, hp⟩
        rw [e] at this; exact this rfl)
    (fun X Q R hp n ⟨hX, hQ⟩ => by
      have e1 : (iprop(X ∗ R) : KW) = R := KW.ext' fun m => ⟨fun h => h.2, fun h => ⟨kw_root hX m, h⟩⟩
      have e2 : (iprop(X ∗ Q) : KW) = Q := KW.ext' fun m => ⟨fun h => h.2, fun h => ⟨kw_root hX m, h⟩⟩
      have := hp n (by rw [e2]; exact hQ)
      rw [e1] at this; exact this)
    (fun h' => (h' none trivial).elim (fun e => e.1 rfl) (fun e => e rfl))
    Unit (fun _ => kwAt true) (fun _ => kwAt false)
    (fun _ _ => .inl ⟨kw_ne_false.2 ⟨some true, ⟨_, ⟨(), rfl⟩, rfl⟩⟩, fun e => by
        have : KW.p (iprop(∃ _ : Unit, kwAt true) : KW) (some false) := by
          rw [e]; exact fun e => nomatch e
        obtain ⟨_, ⟨_, rfl⟩, h⟩ := this
        exact Bool.noConfusion (Option.some.inj h)⟩)
    (fun _ n _ => by
      cases n with
      | some b => exact .inr (fun e => nomatch e)
      | none => refine .inl ⟨kwAt_ne false, fun e => ?_⟩
                have : KW.p kwL (some true) := fun e => nomatch e
                rw [← e] at this
                exact Bool.noConfusion (Option.some.inj this))
    (fun _ _ ⟨h1, h2⟩ => Bool.noConfusion (Option.some.inj (h1.symm.trans h2)))
    (fun _ _ h => ⟨h, h⟩)

-- `Iris.Inv.contradiction'` idx 8: necessary (KW with kwH (True except on False and the leaves, which go to the leaves: intro, idempotent, framing, not monotone), fupd = kwH for both masks, inv i X = pure (X valid), start/finished = the two leaves)
theorem t1c2_24 : ¬ drop0% Iris.Inv.contradiction' 8 := fun h =>
  @h KW _ _ (fun _ X => kwH X) Unit (fun _ X => iprop(⌜X.p none⌝)) (fun _ _ => kwPers _)
    kwH_intro kwH_trans kwH_frame (fun _ h => h)
    (fun P n hp => by
      cases n with
      | some b => exact .inr (fun e => nomatch e)
      | none =>
        refine .inl ⟨kw_ne_false.2 ⟨none, ⟨_, ⟨(), rfl⟩, hp⟩⟩, fun e => ?_⟩
        have : KW.p (iprop(∃ _ : Unit, ⌜P.p none⌝) : KW) none := ⟨_, ⟨(), rfl⟩, hp⟩
        rw [e] at this; exact this rfl)
    (fun X Q R hp n ⟨hX, hQ⟩ => by
      have e1 : (iprop(X ∗ R) : KW) = R := KW.ext' fun m => ⟨fun h => h.2, fun h => ⟨kw_root hX m, h⟩⟩
      have e2 : (iprop(X ∗ Q) : KW) = Q := KW.ext' fun m => ⟨fun h => h.2, fun h => ⟨kw_root hX m, h⟩⟩
      have := hp n (by rw [e2]; exact hQ)
      rw [e1] at this; exact this)
    (fun h' => (h' none trivial).elim (fun e => e.1 rfl) (fun e => e rfl))
    Unit (fun _ => kwAt true) (fun _ => kwAt false) (fun _ => kwPers _)
    (fun _ _ => .inl ⟨kw_ne_false.2 ⟨some true, ⟨_, ⟨(), rfl⟩, rfl⟩⟩, fun e => by
        have : KW.p (iprop(∃ _ : Unit, kwAt true) : KW) (some false) := by
          rw [e]; exact fun e => nomatch e
        obtain ⟨_, ⟨_, rfl⟩, h⟩ := this
        exact Bool.noConfusion (Option.some.inj h)⟩)
    (fun _ n _ => by
      cases n with
      | some b => exact .inr (fun e => nomatch e)
      | none => refine .inl ⟨kwAt_ne false, fun e => ?_⟩
                have : KW.p kwL (some true) := fun e => nomatch e
                rw [← e] at this
                exact Bool.noConfusion (Option.some.inj this))
    (fun _ _ ⟨h1, h2⟩ => Bool.noConfusion (Option.some.inj (h1.symm.trans h2)))

-- `Iris.Inv.invariant_contradiction` idx 7: necessary (KW, fupd M0 = constant False (no intro), fupd M1 X = X ∨ leaves, inv i X = pure (X ≠ False), start = False, finished = True: I holds, B = leaves fails at the root)
theorem t1c2_25 : ¬ drop0% Iris.Inv.invariant_contradiction 7 := fun h => by
  have H := @h KW _ _ kwZ Unit (fun _ X => iprop(⌜X ≠ iprop(False)⌝)) (fun _ _ => kwPers _)
    kwZ_mono kwZ_trans kwZ_frame (fun _ _ _ hp => kwZ_inv hp) Unit (fun _ => iprop(False)) (fun _ => iprop(True))
    (fun _ => kwPers _) (fun _ _ h => h) (fun _ _ h => h.1)
  exact kwZF_root (H (γ := ()) (i := ()) none (kw_ne_false.2 ⟨some true, .inr kwZF_leaf⟩)).2

-- `Iris.Inv.finished_contradiction` idx 7: necessary (KW, fupd M0 = constant False (no intro), fupd M1 X = X ∨ leaves, inv i X = pure (X ≠ False), start = False, finished = True: finished ∗ I holds at the root, B fails there)
theorem t1c2_26 : ¬ drop0% Iris.Inv.finished_contradiction 7 := fun h => by
  have H := @h KW _ _ kwZ Unit (fun _ X => iprop(⌜X ≠ iprop(False)⌝)) (fun _ _ => kwPers _)
    kwZ_trans (fun _ _ _ hp => kwZ_inv hp) Unit (fun _ => iprop(False)) (fun _ => iprop(True))
    (fun _ => kwPers _) (fun _ _ h => h.1) () ()
  exact kwZF_root (H none ⟨trivial, kw_ne_false.2 ⟨some true, .inr kwZF_leaf⟩⟩).2

-- `Iris.Inv.saved_NA` idx 7: necessary (KW, fupd M0 = constant False (no intro), fupd M1 X = X ∨ leaves, inv i X = pure (X ≠ False), start = False, finished = True: A is valid (P = a leaf), saved (A) holds, □(A -∗ fupd M1 False) fails at the root)
theorem t1c2_27 : ¬ drop0% Iris.Inv.saved_NA 7 := fun h => by
  have H := @h KW _ _ kwZ Unit (fun _ X => iprop(⌜X ≠ iprop(False)⌝)) (fun _ _ => kwPers _)
    kwZ_mono kwZ_trans kwZ_frame (fun _ _ _ hp => kwZ_inv hp) Unit (fun _ => iprop(False)) (fun _ => iprop(True))
    (fun _ _ h => h) (fun _ _ h => h.1) (fun _ _ h => ⟨h, h⟩) ()
  have hA : KW.p (Iris.Inv.A kwZ Unit (fun _ X => iprop(⌜X ≠ iprop(False)⌝)) Unit
      (fun _ => iprop(False)) (fun _ => iprop(True)) ()) none :=
    ⟨_, ⟨kwAt true, rfl⟩, ⟨trivial, fun m _ hm => .inr (by rw [show m = some true from hm]; exact fun e => nomatch e)⟩,
      ⟨_, ⟨(), rfl⟩, kw_ne_false.2 ⟨some true, .inr ⟨trivial, trivial, rfl⟩⟩⟩⟩
  exact kwZF_root ((H none ⟨_, ⟨(), rfl⟩, kw_ne_false.2 ⟨none, .inr ⟨trivial, trivial, hA⟩⟩⟩).2 none (.inl rfl) hA)

-- `Iris.Inv.finished_contradiction` idx 2: necessary (GB (non-affine Boolean BI over Bool with xor), fupd = True, inv = True, start = False, finished = True (persistent, not affine): finished ∗ I = True but B = □ True = emp fails at true)
theorem t1c2_28 : ¬ drop0% Iris.Inv.finished_contradiction 2 := fun h => by
  have H := @h GB _ (fun _ _ => iprop(True)) Unit (fun _ _ => iprop(True)) (fun _ _ => gb_true_pers)
    (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ _ _ _ _ => trivial) Unit (fun _ => iprop(False)) (fun _ => iprop(True))
    (fun _ => gb_true_pers) (fun _ _ ⟨_, _, _, ha, _⟩ => ha) () ()
  exact gb_emp_true (H true ⟨true, false, rfl, trivial, trivial⟩).1

-- `Iris.Inv.invariant_contradiction` idx 2: necessary (GB (non-affine Boolean BI over Bool with xor), fupd = True, inv = True, start = False, finished = True (persistent, not affine): I = True but B = emp fails at true)
theorem t1c2_29 : ¬ drop0% Iris.Inv.invariant_contradiction 2 := fun h => by
  have H := @h GB _ (fun _ _ => iprop(True)) Unit (fun _ _ => iprop(True)) (fun _ _ => gb_true_pers)
    (fun _ _ => trivial) (fun _ _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
    Unit (fun _ => iprop(False)) (fun _ => iprop(True)) (fun _ => gb_true_pers) (fun _ _ _ => trivial)
    (fun _ _ ⟨_, _, _, ha, _⟩ => ha)
  exact gb_emp_true (H (γ := ()) (i := ()) true trivial).1

-- `Iris.Inv.saved_NA` idx 2: necessary (GB (non-affine Boolean BI over Bool with xor), fupd = True, inv = True, start = False, finished = True (persistent, not affine): saved (A) = True but notFUpd (A) = emp fails at true)
theorem t1c2_30 : ¬ drop0% Iris.Inv.saved_NA 2 := fun h => by
  have H := @h GB _ (fun _ _ => iprop(True)) Unit (fun _ _ => iprop(True)) (fun _ _ => gb_true_pers)
    (fun _ _ => trivial) (fun _ _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
    Unit (fun _ => iprop(False)) (fun _ => iprop(True)) (fun _ _ _ => trivial)
    (fun _ _ ⟨_, _, _, ha, _⟩ => ha) (fun _ => gb_true_dup) ()
  exact gb_emp_true (H true ⟨_, ⟨(), rfl⟩, trivial⟩).1

-- `Iris.Inv.finished_contradiction` idx 13: necessary (UPred TM, fupd M0 = id, fupd M1 X = X ∨ (own some token), pure invariants inv i X = (X cancels frames up to owning a token: X ∗ Q ⊢ X ∗ R implies Q ⊢ R ∨ tokens; holds for start γ ∨ B by a semantic argument), start = finished = exclusive start token (not persistent); B = □(own token) fails at the start token, whose core is the unit)
theorem t1c2_31 : ¬ drop0% Iris.Inv.finished_contradiction 13 := fun h => by
  have H := @h (UPred TM) _ _ tmF Unit (fun _ X => iprop(⌜tmInv X⌝)) (fun _ _ => inferInstance)
    tmF_intro tmF_trans (fun _ _ _ hp => tmF_inv hp) Nat
    (fun γ => UPred.ownM (tok γ .s)) (fun γ => UPred.ownM (tok γ .s)) tm_ss 0 ()
  have H2 := (sep_emp.2.trans (sep_mono_right (pure_intro (tm_key 0)))).trans H
  obtain ⟨_, h1⟩ := H2 0 ⟨tok 0 .s, ⟨fun k h => by
      revert h; show (if k = 0 then Tk.s else .e) = .bot → False
      split <;> exact fun h => Tk.noConfusion h, 1, fun k hk => by
      show (if k = 0 then Tk.s else .e) = .e
      rw [if_neg (by omega)]⟩⟩ ⟨tmUnit, (tm_op_unit _).symm⟩
  rcases h1 with h1 | h1
  · exact h1
  · exact tmC_unit 0 _ (fun k => by show (if k = 0 then Tk.s else .e).core = .e; split <;> rfl) h1

-- `Iris.Inv.invariant_contradiction` idx 15: necessary (UPred TM, fupd M0 = id, fupd M1 X = X ∨ (own some token), pure invariants inv i X = (X cancels frames up to owning a token: X ∗ Q ⊢ X ∗ R implies Q ⊢ R ∨ tokens; holds for start γ ∨ B by a semantic argument), start = finished = exclusive start token (not persistent); I is a valid pure fact, B fails at the unit)
theorem t1c2_32 : ¬ drop0% Iris.Inv.invariant_contradiction 15 := fun h => by
  have H := @h (UPred TM) _ _ tmF Unit (fun _ X => iprop(⌜tmInv X⌝)) (fun _ _ => inferInstance)
    tmF_intro tmF_mono tmF_trans tmF_frame (fun _ _ _ hp => tmF_inv hp) Nat
    (fun γ => UPred.ownM (tok γ .s)) (fun γ => UPred.ownM (tok γ .s)) (fun _ => .rfl) tm_ss
  have H2 : iprop(emp) ⊢@{UPred TM} Iris.Inv.B tmF := (pure_intro (tm_key 0)).trans (H (γ := 0) (i := ()))
  obtain ⟨_, h1⟩ := H2 0 ⟨tmUnit, ⟨fun _ h => Tk.noConfusion h, 0, fun _ _ => rfl⟩⟩ ⟨tmUnit, (tm_op_unit _).symm⟩
  rcases h1 with h1 | h1
  · exact h1
  · exact tmC_unit 0 _ (fun k => rfl) h1

-- `Iris.Inv.saved_NA` idx 17: necessary (UPred TM, fupd M0 = id, fupd M1 X = X ∨ (own some token), pure cancellation invariants, start = finished = the exclusive (non-duplicable) start token: every saved γ P is a valid pure fact, A holds at the unit via P = False, so emp ⊢ fupd M1 False = own some token, false at the unit)
theorem t1c2_33 : ¬ drop0% Iris.Inv.saved_NA 17 := fun h => by
  have H := @h (UPred TM) _ _ tmF Unit (fun _ X => iprop(⌜tmInv X⌝)) (fun _ _ => inferInstance)
    tmF_intro tmF_mono tmF_trans tmF_frame (fun _ _ _ hp => tmF_inv hp) Nat
    (fun γ => UPred.ownM (tok γ .s)) (fun γ => UPred.ownM (tok γ .s)) (fun _ => .rfl) tm_ss 0
  have hS : ∀ P : UPred TM, iprop(emp) ⊢ Iris.Inv.saved Unit (fun _ X => iprop(⌜tmInv X⌝)) Nat
      (fun γ => UPred.ownM (tok γ .s)) (fun γ => UPred.ownM (tok γ .s)) 0 P := fun P =>
    (pure_intro (tm_key_saved 0 P)).trans (exists_intro (Ψ := fun _ : Unit => iprop(⌜tmInv iprop(UPred.ownM (tok 0 .s) ∨ UPred.ownM (tok 0 .s) ∗ □ P)⌝)) ())
  have nf : iprop(emp) ⊢@{UPred TM} iprop(□ (False -∗ tmF .M1 iprop(False))) :=
    intuitionistically_emp.2.trans (intuitionistically_mono (wand_intro (sep_elim_right.trans false_elim)))
  have hA := emp_sep.2.trans ((sep_mono nf (hS iprop(False))).trans
    (exists_intro (Ψ := fun P => iprop(Iris.Inv.notFUpd tmF P ∗ Iris.Inv.saved Unit (fun _ X => iprop(⌜tmInv X⌝)) Nat
      (fun γ => UPred.ownM (tok γ .s)) (fun γ => UPred.ownM (tok γ .s)) 0 P)) iprop(False)))
  have H2 := (and_intro ((hS _).trans H) hA).trans (persistent_and_sep_mp.trans
    ((sep_mono_left intuitionistically_elim).trans wand_elim_left))
  rcases H2 0 ⟨tmUnit, ⟨fun _ h => Tk.noConfusion h, 0, fun _ _ => rfl⟩⟩ ⟨tmUnit, (tm_op_unit _).symm⟩ with h1 | h1
  · exact h1
  · exact tmC_unit 0 _ (fun k => rfl) h1

-- `Iris.Inv.saved_cast` idx 19: necessary (UPred TM, fupd M0 = id, fupd M1 X = X ∨ (own some token), pure cancellation invariants, start = finished = the exclusive (non-duplicable) start token: saved γ True ∗ saved γ False ∗ □True is valid but fupd M1 (□False) = own some token fails at the unit)
theorem t1c2_34 : ¬ drop0% Iris.Inv.saved_cast 19 := fun h => by
  have H := @h (UPred TM) _ _ iprop(True) iprop(False) tmF Unit (fun _ X => iprop(⌜tmInv X⌝)) (fun _ _ => inferInstance)
    tmF_intro tmF_mono tmF_trans tmF_frame (fun _ _ _ hp => tmF_inv hp) Nat
    (fun γ => UPred.ownM (tok γ .s)) (fun γ => UPred.ownM (tok γ .s)) (fun _ => .rfl) tm_ss 0
  have hS : ∀ P : UPred TM, iprop(emp) ⊢ Iris.Inv.saved Unit (fun _ X => iprop(⌜tmInv X⌝)) Nat
      (fun γ => UPred.ownM (tok γ .s)) (fun γ => UPred.ownM (tok γ .s)) 0 P := fun P =>
    (pure_intro (tm_key_saved 0 P)).trans (exists_intro (Ψ := fun _ : Unit => iprop(⌜tmInv iprop(UPred.ownM (tok 0 .s) ∨ UPred.ownM (tok 0 .s) ∗ □ P)⌝)) ())
  have hT : iprop(emp) ⊢@{UPred TM} iprop(□ True) := intuitionistically_emp.2.trans (intuitionistically_mono true_intro)
  have H2 := (sep_emp.2.trans (sep_mono (hS _) (sep_emp.2.trans (sep_mono (hS _) hT)))).trans H
  rcases H2 0 ⟨tmUnit, ⟨fun _ h => Tk.noConfusion h, 0, fun _ _ => rfl⟩⟩ ⟨tmUnit, (tm_op_unit _).symm⟩ with h1 | h1
  · exact h1.2
  · exact tmC_unit 0 _ (fun k => rfl) h1

-- `Iris.LaterCreditsPlain.contradiction` idx 6: necessary (SiProp with the constant-True fancy update (lawful, from W8c0), lc = True: lc_fupd_elim_later and fupd_keep_si_pure' hold trivially, BILoeb from the Sbi; without lc_soundness nothing forces False)
theorem t1c2_35 : ¬ drop0% Iris.LaterCreditsPlain.contradiction 6 := fun h =>
  @h SiProp _ _ topFupd iprop(True) (fun _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial) inferInstance
