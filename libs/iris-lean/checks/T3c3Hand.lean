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

namespace T3c3
open Iris Iris.BI Iris.Std Iris.ProofMode

/-- A lawful closure modality on a BI (intro, join, frame, absorbs except0). (copied from T2c1) -/
structure LM (PROP : Type _) [BI PROP] where
  M : PROP → PROP
  ne : OFE.NonExpansive M
  mono : ∀ {P Q : PROP}, (P ⊢ Q) → M P ⊢ M Q
  intro : ∀ {P : PROP}, P ⊢ M P
  join : ∀ {P : PROP}, M (M P) ⊢ M P
  frame : ∀ {P R : PROP}, iprop(M P ∗ R) ⊢ M iprop(P ∗ R)
  ex0 : ∀ {P : PROP}, iprop(◇ M P) ⊢ M P

/-- Per-slot states: e (none), o (exclusive), d (duplicable seal), bot (invalid). -/
inductive T3 where | e | o | d | bot
  deriving DecidableEq

def T3.op : T3 → T3 → T3
  | .e, x => x
  | x, .e => x
  | .d, .d => .d
  | _, _ => .bot

theorem T3.op_assoc (a b c : T3) : a.op (b.op c) = (a.op b).op c := by
  cases a <;> cases b <;> cases c <;> rfl
theorem T3.op_comm (a b : T3) : a.op b = b.op a := by cases a <;> cases b <;> rfl
theorem T3.op_bot (a b : T3) (h : a.op b ≠ .bot) : a ≠ .bot := by
  cases a <;> cases b <;> simp_all [T3.op]
theorem T3.e_op (a : T3) : T3.e.op a = a := rfl
theorem T3.op_e (a : T3) : a.op .e = a := by cases a <;> rfl

/-- Extra slots: the invariant content a (= α), the fresh witness, two irreversible seals. -/
inductive X4 where | A | FW | S1 | S2
  deriving DecidableEq

abbrev Idx := Sum Pos X4

/-- RD: mask tokens (inl p) and the extra slots (inr _). -/
structure RD where
  g : Idx → T3

def RD.op (x y : RD) : RD := ⟨fun i => (x.g i).op (y.g i)⟩
def RD.Valid (x : RD) : Prop := ∀ i, x.g i ≠ .bot
def RD.Le (x y : RD) : Prop := ∃ zg : Idx → T3, ∀ i, y.g i = (x.g i).op (zg i)
def rdUnit : RD := ⟨fun _ => .e⟩

instance : OFE RD := OFE.ofDiscrete RD
instance : OFE.Discrete RD := ⟨id⟩

theorem RD.ext' {x y : RD} (h : ∀ i, x.g i = y.g i) : x = y := by
  cases x; cases y; congr; funext i; exact h i
theorem RD.op_assoc (x y z : RD) : x.op (y.op z) = (x.op y).op z := by
  simp only [RD.op, T3.op_assoc]
theorem RD.op_comm (x y : RD) : x.op y = y.op x := by
  simp only [RD.op]; congr 1; funext i; exact T3.op_comm _ _
theorem RD.le_refl (x : RD) : x.Le x := ⟨fun _ => T3.e, fun i => (T3.op_e _).symm⟩
theorem RD.le_op (x z : RD) : z.Le (x.op z) := ⟨x.g, fun i => T3.op_comm _ _⟩
theorem RD.unit_op (x : RD) : rdUnit.op x = x := by cases x; simp only [RD.op, rdUnit, T3.e_op]
theorem RD.op_unit (x : RD) : x.op rdUnit = x := by rw [RD.op_comm]; exact RD.unit_op x

instance rdORA : ORA RD := ORA.ofDiscreteORAData {
  pcore := fun _ => some rdUnit
  op := RD.op
  Valid := RD.Valid
  Order := RD.Le
  assoc := RD.op_assoc
  comm := RD.op_comm
  pcore_op_left := by intro x cx h; cases h; exact RD.unit_op x
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := fun x y h i => T3.op_bot _ _ (h i)
  ord_trans := by
    rintro x y z ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨fun i => (a i).op (b i), fun i => by rw [hb, ha, T3.op_assoc]⟩
  op_mono_left := by
    rintro x y z ⟨a, ha⟩
    refine ⟨a, fun i => ?_⟩
    show ((y.g i).op (z.g i)) = ((x.g i).op (z.g i)).op (a i)
    rw [ha, ← T3.op_assoc, T3.op_comm (a i), T3.op_assoc]
  valid_of_ord := by
    rintro x y ⟨a, ha⟩ hv i
    exact T3.op_bot _ _ (by rw [← ha]; exact hv i)
  pcore_mono := by intro x y cx _ h; cases h; exact ⟨_, rfl, RD.le_refl _⟩
  pcore_order_op := by intro x cx h y; cases h; exact ⟨_, rfl, RD.le_refl _⟩
  pcore_increasing := by intro x cx h y; cases h; exact RD.le_op _ _
  increasing_closed := by intro x y _ _ z; exact RD.le_op _ _ }

instance : OrderRefl RD := ⟨RD.le_refl⟩

instance rdUORA : UORA RD where
  unit := rdUnit
  unit_valid := fun _ h => T3.noConfusion h
  unit_left_id := RD.unit_op _
  pcore_unit := rfl

instance : IncOrd RD := ⟨by rintro x y ⟨z, hz⟩; have hz' : y = x.op z := hz; subst hz'; exact ⟨z.g, fun _ => rfl⟩⟩

open Classical in
noncomputable def tokE (E : CoPset) : RD := ⟨fun i => match i with
  | .inl p => if p ∈ E then .o else .e
  | .inr _ => .e⟩
noncomputable abbrev ownE (E : CoPset) : UPred RD := UPred.ownM (tokE E)

theorem tokE_union {E1 E2 : CoPset} (h : E1 ## E2) : tokE (E1 ∪ E2) = (tokE E1).op (tokE E2) := by
  apply RD.ext'; intro i; rcases i with p | k
  · simp only [tokE, RD.op]
    have hu := (LawfulSet.mem_union (X := E1) (Y := E2) (x := p))
    have hd := h p
    by_cases h1 : p ∈ E1 <;> by_cases h2 : p ∈ E2 <;> simp_all [T3.op]
  · rfl

theorem tokE_diff {E1 E2 : CoPset} (h : E2 ⊆ E1) : tokE E1 = (tokE E2).op (tokE (E1 \ E2)) := by
  apply RD.ext'; intro i; rcases i with p | k
  · simp only [tokE, RD.op]
    have hu := (LawfulSet.mem_diff (X := E1) (Y := E2) (x := p))
    have hs := h p
    by_cases h1 : p ∈ E1 <;> by_cases h2 : p ∈ E2 <;> simp_all [T3.op]
  · rfl

theorem ownM_disj (E1 E2 : CoPset) : UPred.ownM ((tokE E1).op (tokE E2)) ⊢ iprop(⌜E1 ## E2⌝) :=
  fun n x h p ⟨h1, h2⟩ => by
    have hv : RD.Valid ((tokE E1).op (tokE E2)) := ORA.validN_of_ordN h x.property
    have := hv (.inl p)
    simp [RD.op, tokE, h1, h2, T3.op] at this

theorem ownE_join (E1 E2 : CoPset) : iprop(ownE E1 ∗ ownE E2) ⊢ iprop(⌜E1 ## E2⌝ ∧ ownE (E1 ∪ E2)) :=
  (UPred.ownM_op _ _).2.trans <| (and_intro (ownM_disj E1 E2) .rfl).trans <| pure_elim_left fun hd =>
    and_intro (pure_intro hd) (by show _ ⊢ UPred.ownM (tokE (E1 ∪ E2)); rw [tokE_union hd])

theorem ownE_split {E1 E2 : CoPset} (hd : E1 ## E2) : ownE (E1 ∪ E2) ⊢ iprop(ownE E1 ∗ ownE E2) := by
  show UPred.ownM (tokE (E1 ∪ E2)) ⊢ _; rw [tokE_union hd]; exact (UPred.ownM_op _ _).1

theorem ownE_sub {E1 E2 : CoPset} (h : E2 ⊆ E1) : ownE E1 ⊣⊢ iprop(ownE E2 ∗ ownE (E1 \ E2)) := by
  show UPred.ownM (tokE E1) ⊣⊢ _; rw [tokE_diff h]; exact UPred.ownM_op _ _

/-- Fancy update from mask ownership: own E1, get L (own E2 ∗ P). (T2c1's wf, on RD) -/
noncomputable def wf (L : LM (UPred RD)) (E1 E2 : CoPset) (P : UPred RD) : UPred RD :=
  iprop(ownE E1 -∗ L.M iprop(ownE E2 ∗ P))

theorem pa {φ : Prop} {X Y Z : UPred RD} (h : φ → iprop(X ∗ Y) ⊢ Z) : iprop((⌜φ⌝ ∧ X) ∗ Y) ⊢ Z :=
  (sep_mono_left (pure_elim_left fun hφ => wand_intro (h hφ))).trans wand_elim_left

theorem rcomm {A B C : UPred RD} : iprop((A ∗ B) ∗ C) ⊢ iprop((A ∗ C) ∗ B) :=
  sep_assoc.1.trans ((sep_mono_right sep_comm.1).trans sep_assoc.2)

/-- Lawful for every closure modality L (T2c1's proof). -/
@[instance_reducible] noncomputable def wFupd (L : LM (UPred RD)) : BIFUpdate (UPred RD) where
  fupd := wf L
  ne := ⟨fun _ _ _ h => wand_ne.ne .rfl (L.ne.ne (sep_ne.ne .rfl h))⟩
  subset {E1 E2} h := wand_intro <| emp_sep.1.trans <| (ownE_sub h).1.trans <|
    (sep_mono_right (wand_intro ((sep_comm.1.trans (ownE_sub h).2).trans (sep_emp.2.trans L.intro)))).trans L.intro
  except0 := wand_intro <| (sep_mono_right except0_intro).trans
    (except0_sep.2.trans ((except0_mono wand_elim_left).trans L.ex0))
  mono h := wand_intro (wand_elim_left.trans (L.mono (sep_mono_right h)))
  trans := wand_intro (wand_elim_left.trans ((L.mono wand_elim_right).trans L.join))
  mask_frame_right_strong {E1 E2 Ef P} hd := wand_intro <| (sep_mono_right (ownE_split hd)).trans <|
    sep_assoc.2.trans <| (sep_mono_left wand_elim_left).trans <| L.frame.trans <| L.mono <|
      rcomm.trans ((sep_mono_left (ownE_join E2 Ef)).trans (pa fun hd2 => sep_mono_right (pure_imp_elim hd2)))
  frame_right := wand_intro <| rcomm.trans <| (sep_mono_left wand_elim_left).trans <|
    L.frame.trans (L.mono sep_assoc.1)

/-! ### The one-shot invariant store -/

def t1 : RD := ⟨fun i => match i with | .inl p => if p = 1 then .o else .e | .inr _ => .e⟩
def aR : RD := ⟨fun i => match i with | .inr .A => .o | _ => .e⟩
def fwR : RD := ⟨fun i => match i with | .inr .FW => .o | _ => .e⟩
def c1 : RD := ⟨fun i => match i with | .inr .S1 => .d | _ => .e⟩
def c2 : RD := ⟨fun i => match i with | .inr .S2 => .d | _ => .e⟩
/-- Fresh: content inside, both seals unbroken. -/
def wF : RD := ⟨fun i => match i with | .inr .A => .o | .inr .S1 => .o | .inr .S2 => .o | _ => .e⟩
/-- Open: the mask token en₁ and the fresh witness inside, first seal broken. -/
def wO : RD := ⟨fun i => match i with
  | .inl p => if p = 1 then .o else .e
  | .inr .FW => .o | .inr .S1 => .d | .inr .S2 => .o | _ => .e⟩
/-- Sealed: content and fresh witness locked inside, both seals broken. -/
def wS : RD := ⟨fun i => match i with
  | .inr .A => .o | .inr .FW => .o | .inr .S1 => .d | .inr .S2 => .d | _ => .e⟩

noncomputable def W : UPred RD := iprop(UPred.ownM wF ∨ UPred.ownM wO ∨ UPred.ownM wS)

/-- State-passing closure through the store W. -/
noncomputable def LW : LM (UPred RD) where
  M Q := iprop(W -∗ |==> ◇ (W ∗ Q))
  ne := ⟨fun _ _ _ h => wand_ne.ne .rfl (bupd_ne.ne (or_ne.ne .rfl (sep_ne.ne .rfl h)))⟩
  mono h := wand_mono_right (BIUpdate.mono (except0_mono (sep_mono_right h)))
  intro := wand_intro (sep_comm.1.trans (except0_intro.trans BIUpdate.intro))
  join := wand_intro <| wand_elim_left.trans <|
    (BIUpdate.mono (except0_mono (sep_comm.1.trans wand_elim_left))).trans <|
    (BIUpdate.mono except0_bupd).trans <| BIUpdate.trans.trans (BIUpdate.mono except0_idem.1)
  frame := wand_intro <| rcomm.trans <| (sep_mono_left wand_elim_left).trans <|
    BIUpdate.frame_right.trans (BIUpdate.mono (except0_frame_right.trans (except0_mono sep_assoc.1)))
  ex0 := wand_intro <| (sep_mono_right except0_intro).trans <| except0_sep.2.trans <|
    (except0_mono wand_elim_left).trans <| except0_bupd.trans (BIUpdate.mono except0_idem.1)


/-! ### Resource facts -/

theorem tokE_one : tokE {1} = t1 := by
  apply RD.ext'; intro i; rcases i with p | k
  · by_cases h : p = 1
    · subst h; simp [tokE, t1, LawfulSet.mem_singleton]
    · simp [tokE, t1, h, LawfulSet.mem_singleton]
  · rfl

theorem tokE_empty : tokE ∅ = rdUnit := by
  apply RD.ext'; intro i; rcases i with p | k
  · by_cases h : p ∈ (∅ : CoPset)
    · exact (CoPset.mem_empty h).elim
    · simp [tokE, rdUnit, h]
  · rfl

theorem e1 : ownE {1} ⊣⊢ UPred.ownM t1 := by
  show UPred.ownM (tokE {1}) ⊣⊢ _; rw [tokE_one]; exact ⟨.rfl, .rfl⟩

theorem e0 {P : UPred RD} : P ⊢ ownE ∅ := fun _ x _ => by
  show RD.Le (tokE ∅) x.val; rw [tokE_empty]; exact ⟨x.val.g, fun _ => rfl⟩

theorem own_bad {z : RD} (i : Idx) (h : z.g i = .bot) : UPred.ownM z ⊢ iprop(False) :=
  fun _ x hx => (ORA.validN_of_ordN hx x.property : RD.Valid z) i h

theorem sep_bad {x y : RD} (i : Idx) (h : (x.op y).g i = .bot) :
    iprop(UPred.ownM x ∗ UPred.ownM y) ⊢ iprop(False) :=
  (UPred.ownM_op _ _).2.trans (own_bad i h)

theorem own_dup {x c : RD} (h : x.op c = x) : UPred.ownM x ⊢ iprop(UPred.ownM x ∗ UPred.ownM c) :=
  (show UPred.ownM x ⊢ UPred.ownM (x.op c) by rw [h]).trans (UPred.ownM_op _ _).1

theorem wO_c1 : wO.op c1 = wO := by
  apply RD.ext'; intro i; rcases i with p | k
  · by_cases h : p = 1 <;> simp [RD.op, wO, c1, h, T3.op]
  · cases k <;> rfl
theorem wS_c2 : wS.op c2 = wS := by
  apply RD.ext'; intro i; rcases i with p | k
  · rfl
  · cases k <;> rfl

/-- Pointwise "frame-preserving" step on a slot. -/
def Ok (a b : T3) : Prop := ∀ c : T3, a.op c ≠ .bot → b.op c ≠ .bot
theorem okR (a : T3) : Ok a a := fun _ h => h
theorem ok_od : Ok .o .d := fun c h => by cases c <;> simp_all [T3.op]

theorem upd_of {x y : RD} (h : ∀ i, Ok (x.g i) (y.g i)) : x ~~> y := by
  intro n mz hv
  cases mz with
  | none =>
    have hv' : RD.Valid (x.op rdUnit) := by rw [RD.op_unit]; exact hv
    have : RD.Valid (y.op rdUnit) := fun i => h i _ (hv' i)
    rw [RD.op_unit] at this; exact this
  | some z => exact fun i => h i (z.g i) (hv i)

theorem upd1 : (t1.op (fwR.op wF)) ~~> (wO.op aR) := upd_of fun i => by
  rcases i with p | k
  · by_cases h : p = 1
    · subst h; simp [RD.op, t1, fwR, wF, wO, aR, T3.op]; exact okR _
    · simp [RD.op, t1, fwR, wF, wO, aR, h, T3.op]; exact okR _
  · cases k
    · exact okR _
    · exact okR _
    · exact ok_od
    · exact okR _

theorem upd2 : (aR.op wO) ~~> (wS.op t1) := upd_of fun i => by
  rcases i with p | k
  · by_cases h : p = 1
    · subst h; simp [RD.op, t1, wS, wO, aR, T3.op]; exact okR _
    · simp [RD.op, t1, wS, wO, aR, h, T3.op]; exact okR _
  · cases k
    · exact okR _
    · exact okR _
    · exact okR _
    · exact ok_od

theorem Wcases {R C : UPred RD} (h1 : iprop(UPred.ownM wF ∗ R) ⊢ C) (h2 : iprop(UPred.ownM wO ∗ R) ⊢ C)
    (h3 : iprop(UPred.ownM wS ∗ R) ⊢ C) : iprop(W ∗ R) ⊢ C :=
  sep_or_right.1.trans (or_elim h1 (sep_or_right.1.trans (or_elim h2 h3)))

theorem fF {P : UPred RD} : iprop(False) ⊢ P := false_elim

/-! ### Modal plumbing -/

theorem UU {P : UPred RD} : iprop(|==> ◇ |==> ◇ P) ⊢ iprop(|==> ◇ P) :=
  (BIUpdate.mono except0_bupd).trans (BIUpdate.trans.trans (BIUpdate.mono except0_idem.1))

theorem fr {R P : UPred RD} : iprop(R ∗ |==> ◇ P) ⊢ iprop(|==> ◇ (R ∗ P)) :=
  sep_comm.1.trans (BIUpdate.frame_right.trans (BIUpdate.mono (except0_frame_right.trans (except0_mono sep_comm.1))))

theorem wfE {E1 E2 : CoPset} {P : UPred RD} :
    iprop(wf LW E1 E2 P ∗ (ownE E1 ∗ W)) ⊢ iprop(|==> ◇ (W ∗ (ownE E2 ∗ P))) :=
  sep_assoc.2.trans ((sep_mono_left wand_elim_left).trans wand_elim_left)

/-! ### The accessor with α := own a, empty telescopes, commit impossible -/

noncomputable def accU (P : UPred RD) : UPred RD :=
  wf LW {1} ∅ iprop(UPred.ownM aR ∗ ((UPred.ownM aR -∗ wf LW ∅ {1} P) ∧ (False -∗ wf LW ∅ {1} iprop(False))))

theorem wf_mono {E1 E2 : CoPset} {P Q : UPred RD} (h : P ⊢ Q) : wf LW E1 E2 P ⊢ wf LW E1 E2 Q :=
  wand_mono_right (LW.mono (sep_mono_right h))

theorem accU_mono {P Q : UPred RD} (h : P ⊢ Q) : accU P ⊢ accU Q :=
  wf_mono (sep_mono_right (and_mono_left (wand_mono_right (wf_mono h))))

theorem toW_O : UPred.ownM wO ⊢ W := or_intro_l.trans or_intro_r
theorem toW_S : UPred.ownM wS ⊢ W := or_intro_r.trans or_intro_r
theorem toW_F : UPred.ownM wF ⊢ W := or_intro_l

/-- The abort closure: give a back, close (seal the store for good), get en₁ back. -/
theorem abortP : (iprop(emp) : UPred RD) ⊢ iprop(UPred.ownM aR -∗ wf LW ∅ {1} iprop(emp)) := by
  refine wand_intro (wand_intro (wand_intro ?_))
  refine (sep_mono_left (sep_elim_left.trans emp_sep.1)).trans ?_
  refine sep_comm.1.trans (Wcases ((sep_bad (.inr .A) rfl).trans fF) ?_ ((sep_bad (.inr .A) rfl).trans fF))
  refine (sep_comm.1.trans (UPred.ownM_op _ _).2).trans ((UPred.bupd_ownM_update upd2).trans (BIUpdate.mono ?_))
  exact (UPred.ownM_op _ _).1.trans ((sep_mono toW_S (e1.2.trans sep_emp.2)).trans except0_intro)

theorem commitP : (iprop(emp) : UPred RD) ⊢ iprop(False -∗ wf LW ∅ {1} iprop(False)) :=
  wand_intro (sep_elim_right.trans false_elim)

/-- One round works from the fresh witness. -/
theorem posA : UPred.ownM fwR ⊢ accU iprop(emp) := by
  refine wand_intro (wand_intro ?_)
  -- (fw ∗ ownE {1}) ∗ W ⊢ |==> ◇ (W ∗ (ownE ∅ ∗ Body))
  refine rcomm.trans ?_
  have hW : iprop(UPred.ownM fwR ∗ W) ⊢ iprop(UPred.ownM fwR ∗ UPred.ownM wF) :=
    sep_comm.1.trans (Wcases sep_comm.1 ((sep_bad (.inr .FW) rfl).trans fF) ((sep_bad (.inr .FW) rfl).trans fF))
  refine (sep_mono hW e1.1).trans ?_
  refine (sep_comm.1.trans ((sep_mono_right (UPred.ownM_op _ _).2).trans (UPred.ownM_op _ _).2)).trans ?_
  refine (UPred.bupd_ownM_update upd1).trans (BIUpdate.mono ?_)
  refine (UPred.ownM_op _ _).1.trans ((sep_mono toW_O ?_).trans except0_intro)
  exact emp_sep.2.trans (sep_mono e0 (sep_emp.2.trans (sep_mono_right (and_intro abortP commitP))))

theorem r4 {A B C D : UPred RD} : iprop(A ∗ (B ∗ (C ∗ D))) ⊢ iprop((A ∗ C) ∗ (B ∗ D)) :=
  (sep_mono_right (sep_assoc.2.trans ((sep_mono_left sep_comm.1).trans sep_assoc.1))).trans sep_assoc.2

/-- Second round after sealing: W ∗ a with the second seal broken is impossible. -/
theorem inner3 {E R : UPred RD} : iprop(UPred.ownM c2 ∗ (W ∗ (E ∗ (UPred.ownM aR ∗ R)))) ⊢ iprop(False) := by
  have h : iprop(UPred.ownM c2 ∗ (W ∗ (E ∗ (UPred.ownM aR ∗ R)))) ⊢ iprop(W ∗ (UPred.ownM c2 ∗ UPred.ownM aR)) := by
    iintro ⟨Hc, HW, -, Ha, -⟩
    isplitl [HW]
    · iexact HW
    · isplitl [Hc]
      · iexact Hc
      · iexact Ha
  refine h.trans (Wcases ?_ ?_ ?_)
  · exact (sep_mono_right sep_elim_right).trans (sep_bad (.inr .A) rfl)
  · exact (sep_mono_right sep_elim_left).trans (sep_bad (.inr .S2) rfl)
  · exact (sep_mono_right sep_elim_right).trans (sep_bad (.inr .A) rfl)

/-- After the abort the store is Sealed (first seal broken, en₁ outside); run the second round. -/
theorem inner2 {X : UPred RD} (hX : X ⊢ accU iprop(True)) :
    iprop(UPred.ownM c1 ∗ (W ∗ (ownE {1} ∗ X))) ⊢ iprop(|==> ◇ False) := by
  have h : iprop(UPred.ownM c1 ∗ (W ∗ (ownE {1} ∗ X))) ⊢ iprop((W ∗ (UPred.ownM c1 ∗ ownE {1})) ∗ X) := by
    iintro ⟨Hc, HW, HE, HX⟩
    isplitl [HW Hc HE]
    · isplitl [HW]
      · iexact HW
      · isplitl [Hc]
        · iexact Hc
        · iexact HE
    · iexact HX
  have hS : iprop(W ∗ (UPred.ownM c1 ∗ ownE {1})) ⊢ iprop(UPred.ownM wS ∗ ownE {1}) := by
    refine Wcases ?_ ?_ (sep_mono_right sep_elim_right)
    · exact ((sep_mono_right sep_elim_left).trans (sep_bad (.inr .S1) rfl)).trans fF
    · exact ((sep_mono_right (sep_elim_right.trans e1.1)).trans (sep_bad (.inl 1) (by simp [RD.op, wO, t1, T3.op]))).trans fF
  refine (h.trans (sep_mono_left hS)).trans ?_
  refine (sep_mono_left (sep_mono_left ((own_dup wS_c2).trans (sep_comm.1.trans (sep_mono_right toW_S))))).trans ?_
  have h2 : iprop(((UPred.ownM c2 ∗ W) ∗ ownE {1}) ∗ X) ⊢ iprop(UPred.ownM c2 ∗ (X ∗ (ownE {1} ∗ W))) := by
    iintro ⟨⟨⟨Hc, HW⟩, HE⟩, HX⟩
    isplitl [Hc]
    · iexact Hc
    · isplitl [HX]
      · iexact HX
      · isplitl [HE]
        · iexact HE
        · iexact HW
  refine h2.trans ((sep_mono_right ((sep_mono_left hX).trans wfE)).trans (fr.trans (BIUpdate.mono (except0_mono inner3))))

/-- First round: the store must be Open (a outside), keep a copy of the broken first seal, abort. -/
theorem inner1 {X : UPred RD} (hX : X ⊢ accU iprop(True)) :
    iprop(W ∗ (ownE ∅ ∗ (UPred.ownM aR ∗ ((UPred.ownM aR -∗ wf LW ∅ {1} X) ∧ (False -∗ wf LW ∅ {1} iprop(False))))))
      ⊢ iprop(|==> ◇ False) := by
  refine (sep_mono_right (sep_mono_right (sep_mono_right and_elim_l))).trans (r4.trans ?_)
  have hO : iprop(W ∗ UPred.ownM aR) ⊢ iprop((UPred.ownM c1 ∗ W) ∗ UPred.ownM aR) :=
    (Wcases ((sep_bad (.inr .A) rfl).trans fF) .rfl ((sep_bad (.inr .A) rfl).trans fF)).trans
      (sep_mono_left ((own_dup wO_c1).trans (sep_comm.1.trans (sep_mono_right toW_O))))
  refine (sep_mono_left hO).trans ?_
  have h : iprop(((UPred.ownM c1 ∗ W) ∗ UPred.ownM aR) ∗ (ownE ∅ ∗ (UPred.ownM aR -∗ wf LW ∅ {1} X)))
      ⊢ iprop(UPred.ownM c1 ∗ (((UPred.ownM aR -∗ wf LW ∅ {1} X) ∗ UPred.ownM aR) ∗ (ownE ∅ ∗ W))) := by
    iintro ⟨⟨⟨Hc, HW⟩, Ha⟩, HE, HAb⟩
    isplitl [Hc]
    · iexact Hc
    · isplitl [HAb Ha]
      · isplitl [HAb]
        · iexact HAb
        · iexact Ha
      · isplitl [HE]
        · iexact HE
        · iexact HW
  refine h.trans ((sep_mono_right ((sep_mono_left wand_elim_left).trans wfE)).trans (fr.trans ?_))
  exact (BIUpdate.mono (except0_mono (inner2 hX))).trans UU

def x0 : RD := t1.op (fwR.op wF)

theorem x0_valid : RD.Valid x0 := fun i => by
  rcases i with p | k
  · by_cases h : p = 1
    · subst h; simp [x0, RD.op, t1, fwR, wF, T3.op]
    · simp [x0, RD.op, t1, fwR, wF, h, T3.op]
  · cases k <;> simp [x0, RD.op, t1, fwR, wF, T3.op]

theorem no_bupd_false : ¬ (UPred.ownM x0 ⊢ iprop(|==> ◇ False)) := fun h => by
  have hv : ✓{1} (x0 • (UORA.unit : RD)) := by
    show RD.Valid (x0.op rdUnit); rw [RD.op_unit]; exact x0_valid
  obtain ⟨_, _, hx⟩ := h 1 ⟨x0, x0_valid⟩ (RD.le_refl _) 1 UORA.unit (Nat.le_refl 1) hv
  rcases hx with hx | hx
  · exact hx
  · exact hx

/-- Two rounds from the fresh witness are impossible. -/
theorem negA (H : UPred.ownM fwR ⊢ accU (accU iprop(True))) : False := by
  refine no_bupd_false ?_
  have S0 : UPred.ownM x0 ⊢ iprop(UPred.ownM fwR ∗ (ownE {1} ∗ W)) := by
    refine (UPred.ownM_op _ _).1.trans ((sep_mono_right (UPred.ownM_op _ _).1).trans ?_)
    refine (sep_assoc.2.trans ((sep_mono_left sep_comm.1).trans sep_assoc.1)).trans ?_
    exact sep_mono_right (sep_mono e1.2 toW_F)
  exact S0.trans ((sep_mono_left H).trans (wfE.trans ((BIUpdate.mono (except0_mono (inner1 .rfl))).trans UU)))


/-! ### The rows: α := own a, β = Φ := False, empty telescopes, Eo = {1}, Ei = ∅ -/

noncomputable def αA : Tele.Arg Tele.nil.{0} → UPred RD := fun _ => UPred.ownM aR
def βA : Tele.Arg Tele.nil.{0} → Tele.Arg Tele.nil.{0} → UPred RD := fun _ _ => iprop(False)

noncomputable abbrev AU : UPred RD :=
  @atomic_update (UPred RD) _ (wFupd LW) Tele.nil.{0} Tele.nil.{0} {1} ∅ αA βA βA

theorem negAU (H : UPred.ownM fwR ⊢ AU) : False := by
  letI : BIFUpdate (UPred RD) := wFupd LW
  have u : AU ⊢ accU AU := aupd_unfold.mp
  exact negA (H.trans (u.trans (accU_mono (u.trans (accU_mono true_intro)))))

-- `Iris.tac_aupd_intro` idx 13: necessary
theorem t3c3_0 : ¬ drop0% Iris.tac_aupd_intro 13 := fun h => by
  letI : BIFUpdate (UPred RD) := wFupd LW
  exact negAU (@h (UPred RD) _ (wFupd LW) Tele.nil.{0} Tele.nil.{0} (UPred.ownM fwR) iprop(emp) iprop(emp) {1} ∅ αA βA βA
    intuitionistically_emp.2 posA)

-- `Iris.tac_aupd_intro` idx 14: necessary
theorem t3c3_1 : ¬ drop0% Iris.tac_aupd_intro 14 := fun h => by
  letI : BIFUpdate (UPred RD) := wFupd LW
  exact negAU (@h (UPred RD) _ (wFupd LW) Tele.nil.{0} Tele.nil.{0} (UPred.ownM fwR) (UPred.ownM fwR) iprop(emp) {1} ∅ αA βA βA
    ⟨sep_emp.2, sep_emp.1⟩ posA)

-- `Iris.aupd_intro` idx 13: necessary
theorem t3c3_2 : ¬ drop0% Iris.aupd_intro 13 := fun h => by
  letI : BIFUpdate (UPred RD) := wFupd LW
  have h1 := @h (UPred RD) _ (wFupd LW) Tele.nil.{0} Tele.nil.{0} {1} ∅ (UPred.ownM fwR) iprop(emp) αA βA βA inferInstance
    (and_elim_l.trans posA)
  exact negAU ((and_intro .rfl affine).trans h1)

end T3c3
