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

namespace T3c4
open Iris Iris.BI Iris.Std

/-- A lawful closure modality on a BI (intro, join, frame, absorbs except0). (copied from T2c1) -/
structure LM (PROP : Type _) [BI PROP] where
  M : PROP → PROP
  ne : OFE.NonExpansive M
  mono : ∀ {P Q : PROP}, (P ⊢ Q) → M P ⊢ M Q
  intro : ∀ {P : PROP}, P ⊢ M P
  join : ∀ {P : PROP}, M (M P) ⊢ M P
  frame : ∀ {P R : PROP}, iprop(M P ∗ R) ⊢ M iprop(P ∗ R)
  ex0 : ∀ {P : PROP}, iprop(◇ M P) ⊢ M P

/-- Mask slot: e (not owned), o (owned, exclusive), bot (invalid). -/
inductive M2 where | e | o | bot
  deriving DecidableEq

def M2.op : M2 → M2 → M2
  | .e, x => x
  | x, .e => x
  | _, _ => .bot

theorem M2.op_assoc (a b c : M2) : a.op (b.op c) = (a.op b).op c := by
  cases a <;> cases b <;> cases c <;> rfl
theorem M2.op_comm (a b : M2) : a.op b = b.op a := by cases a <;> cases b <;> rfl

/-- Store state: n (no state token), f (fresh), o (open), d (sealed), bot (invalid). -/
inductive S5 where | n | f | o | d | bot
  deriving DecidableEq

def S5.op : S5 → S5 → S5
  | .n, x => x
  | x, .n => x
  | _, _ => .bot

theorem S5.op_assoc (a b c : S5) : a.op (b.op c) = (a.op b).op c := by
  cases a <;> cases b <;> cases c <;> rfl
theorem S5.op_comm (a b : S5) : a.op b = b.op a := by cases a <;> cases b <;> rfl

/-- RC: exact resources (mask tokens and one state token); open excludes owning name 1. -/
structure RC where
  m : Pos → M2
  s : S5

def RC.op (x y : RC) : RC := ⟨fun p => (x.m p).op (y.m p), x.s.op y.s⟩
def RC.Valid (x : RC) : Prop := (∀ p, x.m p ≠ .bot) ∧ x.s ≠ .bot ∧ (x.s = .o → x.m 1 = .e)
def rcUnit : RC := ⟨fun _ => .e, .n⟩

theorem RC.ext' {x y : RC} (hm : ∀ p, x.m p = y.m p) (hs : x.s = y.s) : x = y := by
  cases x; cases y; simp only at hm hs; subst hs; congr; funext p; exact hm p

theorem RC.op_assoc (x y z : RC) : x.op (y.op z) = (x.op y).op z :=
  RC.ext' (fun p => M2.op_assoc _ _ _) (S5.op_assoc _ _ _)
theorem RC.op_comm (x y : RC) : x.op y = y.op x :=
  RC.ext' (fun p => M2.op_comm _ _) (S5.op_comm _ _)
theorem RC.unit_op (x : RC) : rcUnit.op x = x := RC.ext' (fun _ => rfl) rfl
theorem RC.op_unit (x : RC) : x.op rcUnit = x := by rw [RC.op_comm]; exact RC.unit_op x

theorem M2.op_bot {a b : M2} (h : a.op b ≠ .bot) : a ≠ .bot := by cases a <;> cases b <;> simp_all [M2.op]
theorem S5.op_bot {a b : S5} (h : a.op b ≠ .bot) : a ≠ .bot := by cases a <;> cases b <;> simp_all [S5.op]

theorem RC.valid_op_left {x y : RC} (h : (x.op y).Valid) : x.Valid := by
  obtain ⟨hm, hs, ho⟩ := h
  refine ⟨fun p => M2.op_bot (hm p), S5.op_bot hs, fun hx => ?_⟩
  have hy : y.s = .n := by
    revert hs; show (x.s.op y.s ≠ .bot → y.s = .n); rw [hx]; cases y.s <;> simp [S5.op]
  have h1 := ho (by show x.s.op y.s = .o; rw [hx, hy]; rfl)
  revert h1; show ((x.m 1).op (y.m 1) = .e → x.m 1 = .e)
  cases x.m 1 <;> cases y.m 1 <;> simp [M2.op]

instance : OFE RC := OFE.ofDiscrete RC
instance : OFE.Discrete RC := ⟨id⟩

instance rcORA : ORA RC := ORA.ofDiscreteORAData {
  pcore := fun _ => some rcUnit
  op := RC.op
  Valid := RC.Valid
  Order := Eq
  assoc := RC.op_assoc
  comm := RC.op_comm
  pcore_op_left := by intro x cx h; cases h; exact RC.unit_op x
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := fun _ _ h => RC.valid_op_left h
  ord_trans := fun _ _ _ h1 h2 => h1.trans h2
  op_mono_left := by intro x y z h; cases h; rfl
  valid_of_ord := by intro x y h hv; cases h; exact hv
  pcore_mono := by intro x y cx h1 h2; exact ⟨rcUnit, rfl, by cases h2; rfl⟩
  pcore_order_op := by intro x cx h y; exact ⟨rcUnit, rfl, by cases h; rfl⟩
  pcore_increasing := by intro x cx h y; cases h; first | exact (RC.unit_op y).symm | exact RC.unit_op y
  increasing_closed := by intro x y _ h; cases h; assumption }

instance : OrderRefl RC := ⟨fun x => show x = x from rfl⟩

instance rcUORA : UORA RC where
  unit := rcUnit
  unit_valid := ⟨fun _ h => M2.noConfusion h, fun h => S5.noConfusion h, fun h => S5.noConfusion h⟩
  unit_left_id := RC.unit_op _
  pcore_unit := rfl

open Classical in
noncomputable def tokE (E : CoPset) : RC := ⟨fun p => if p ∈ E then .o else .e, .n⟩
noncomputable abbrev ownE (E : CoPset) : UPred RC := UPred.ownM (tokE E)

theorem tokE_union {E1 E2 : CoPset} (h : E1 ## E2) : tokE (E1 ∪ E2) = (tokE E1).op (tokE E2) := by
  refine RC.ext' (fun p => ?_) rfl
  simp only [tokE, RC.op]
  have hu := (LawfulSet.mem_union (X := E1) (Y := E2) (x := p))
  have hd := h p
  by_cases h1 : p ∈ E1 <;> by_cases h2 : p ∈ E2 <;> simp_all [M2.op]

theorem tokE_diff {E1 E2 : CoPset} (h : E2 ⊆ E1) : tokE E1 = (tokE E2).op (tokE (E1 \ E2)) := by
  refine RC.ext' (fun p => ?_) rfl
  simp only [tokE, RC.op]
  have hu := (LawfulSet.mem_diff (X := E1) (Y := E2) (x := p))
  have hs := h p
  by_cases h1 : p ∈ E1 <;> by_cases h2 : p ∈ E2 <;> simp_all [M2.op]

theorem ownM_disj (E1 E2 : CoPset) : UPred.ownM ((tokE E1).op (tokE E2)) ⊢ iprop(⌜E1 ## E2⌝) :=
  fun n x h p ⟨h1, h2⟩ => by
    have hv : RC.Valid ((tokE E1).op (tokE E2)) := ORA.validN_of_ordN h x.property
    have := hv.1 p
    simp [RC.op, tokE, h1, h2, M2.op] at this

theorem ownE_join (E1 E2 : CoPset) : iprop(ownE E1 ∗ ownE E2) ⊢ iprop(⌜E1 ## E2⌝ ∧ ownE (E1 ∪ E2)) :=
  (UPred.ownM_op _ _).2.trans <| (and_intro (ownM_disj E1 E2) .rfl).trans <| pure_elim_left fun hd =>
    and_intro (pure_intro hd) (by show _ ⊢ UPred.ownM (tokE (E1 ∪ E2)); rw [tokE_union hd])

theorem ownE_split {E1 E2 : CoPset} (hd : E1 ## E2) : ownE (E1 ∪ E2) ⊢ iprop(ownE E1 ∗ ownE E2) := by
  show UPred.ownM (tokE (E1 ∪ E2)) ⊢ _; rw [tokE_union hd]; exact (UPred.ownM_op _ _).1

theorem ownE_sub {E1 E2 : CoPset} (h : E2 ⊆ E1) : ownE E1 ⊣⊢ iprop(ownE E2 ∗ ownE (E1 \ E2)) := by
  show UPred.ownM (tokE E1) ⊣⊢ _; rw [tokE_diff h]; exact UPred.ownM_op _ _

/-- Fancy update from mask ownership: own E1, get L (own E2 ∗ P). (T2c1's wf, on RC) -/
noncomputable def wf (L : LM (UPred RC)) (E1 E2 : CoPset) (P : UPred RC) : UPred RC :=
  iprop(ownE E1 -∗ L.M iprop(ownE E2 ∗ P))

theorem pa {φ : Prop} {X Y Z : UPred RC} (h : φ → iprop(X ∗ Y) ⊢ Z) : iprop((⌜φ⌝ ∧ X) ∗ Y) ⊢ Z :=
  (sep_mono_left (pure_elim_left fun hφ => wand_intro (h hφ))).trans wand_elim_left

theorem rcomm {A B C : UPred RC} : iprop((A ∗ B) ∗ C) ⊢ iprop((A ∗ C) ∗ B) :=
  sep_assoc.1.trans ((sep_mono_right sep_comm.1).trans sep_assoc.2)

/-- Lawful for every closure modality L (T2c1's proof; it uses no affinity). -/
@[instance_reducible] noncomputable def wFupd (L : LM (UPred RC)) : BIFUpdate (UPred RC) where
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

/-! ### Irreversible store transitions: open (f → o, give up name 1), seal (o → d, take name 1) -/

def openS (x : RC) : RC := ⟨fun p => if p = 1 then .e else x.m p, .o⟩
def sealS (x : RC) : RC := ⟨fun p => if p = 1 then .o else x.m p, .d⟩

def Reach (x y : RC) : Prop :=
  y = x ∨ (x.s = .f ∧ x.m 1 = .o ∧ (y = openS x ∨ y = sealS (openS x))) ∨ (x.s = .o ∧ y = sealS x)

theorem Reach.trans {x y z : RC} (h1 : Reach x y) (h2 : Reach y z) : Reach x z := by
  rcases h1 with rfl | ⟨hs, hm, rfl | rfl⟩ | ⟨hs, rfl⟩
  · exact h2
  · rcases h2 with rfl | ⟨hs', _, _⟩ | ⟨_, rfl⟩
    · exact .inr (.inl ⟨hs, hm, .inl rfl⟩)
    · simp [openS] at hs'
    · exact .inr (.inl ⟨hs, hm, .inr rfl⟩)
  · rcases h2 with rfl | ⟨hs', _, _⟩ | ⟨hs', _⟩
    · exact .inr (.inl ⟨hs, hm, .inr rfl⟩)
    · simp [sealS] at hs'
    · simp [sealS] at hs'
  · rcases h2 with rfl | ⟨hs', _, _⟩ | ⟨hs', _⟩
    · exact .inr (.inr ⟨hs, rfl⟩)
    · simp [sealS] at hs'
    · simp [sealS] at hs'

theorem openS_op {x z : RC} (hs : x.s = .f) (hm : x.m 1 = .o) (hv : (x.op z).Valid) :
    (openS x).op z = openS (x.op z) ∧ ((openS x).op z).Valid ∧ (x.op z).s = .f ∧ (x.op z).m 1 = .o := by
  have hz1 : z.m 1 = .e := by
    have := hv.1 1; revert this; show (x.m 1).op (z.m 1) ≠ .bot → z.m 1 = .e
    rw [hm]; cases z.m 1 <;> simp [M2.op]
  have hzs : z.s = .n := by
    have := hv.2.1; revert this; show x.s.op z.s ≠ .bot → z.s = .n
    rw [hs]; cases z.s <;> simp [S5.op]
  refine ⟨RC.ext' (fun p => ?_) ?_, ⟨fun p => ?_, ?_, fun _ => ?_⟩, ?_, ?_⟩
  · by_cases hp : p = 1
    · subst hp; simp [RC.op, openS, hz1, M2.op]
    · simp [RC.op, openS, hp]
  · simp [RC.op, openS, hzs, S5.op]
  · by_cases hp : p = 1
    · subst hp; simp [RC.op, openS, hz1, M2.op]
    · have := hv.1 p; simpa [RC.op, openS, hp] using this
  · simp [RC.op, openS, hzs, S5.op]
  · simp [RC.op, openS, hz1, M2.op]
  · simp [RC.op, hs, hzs, S5.op]
  · simp [RC.op, hm, hz1, M2.op]

theorem sealS_op {x z : RC} (hs : x.s = .o) (hv : (x.op z).Valid) :
    (sealS x).op z = sealS (x.op z) ∧ ((sealS x).op z).Valid ∧ (x.op z).s = .o := by
  have hzs : z.s = .n := by
    have := hv.2.1; revert this; show x.s.op z.s ≠ .bot → z.s = .n
    rw [hs]; cases z.s <;> simp [S5.op]
  have hxs : (x.op z).s = .o := by show x.s.op z.s = .o; rw [hs, hzs]; rfl
  have h1 : (x.m 1).op (z.m 1) = .e := hv.2.2 hxs
  have hz1 : z.m 1 = .e := by revert h1; cases x.m 1 <;> cases z.m 1 <;> simp [M2.op]
  refine ⟨RC.ext' (fun p => ?_) ?_, ⟨fun p => ?_, ?_, fun h => ?_⟩, hxs⟩
  · by_cases hp : p = 1
    · subst hp; simp [RC.op, sealS, hz1, M2.op]
    · simp [RC.op, sealS, hp]
  · simp [RC.op, sealS, hzs, S5.op]
  · by_cases hp : p = 1
    · subst hp; simp [RC.op, sealS, hz1, M2.op]
    · have := hv.1 p; simpa [RC.op, sealS, hp] using this
  · simp [RC.op, sealS, hzs, S5.op]
  · simp [RC.op, sealS, hzs, S5.op] at h

theorem Reach_frame {x y z : RC} (h : Reach x y) (hv : (x.op z).Valid) :
    (y.op z).Valid ∧ Reach (x.op z) (y.op z) := by
  rcases h with rfl | ⟨hs, hm, rfl | rfl⟩ | ⟨hs, rfl⟩
  · exact ⟨hv, .inl rfl⟩
  · obtain ⟨he, hv', hs', hm'⟩ := openS_op hs hm hv
    exact ⟨hv', he ▸ .inr (.inl ⟨hs', hm', .inl rfl⟩)⟩
  · obtain ⟨he, hv', hs', hm'⟩ := openS_op hs hm hv
    obtain ⟨he2, hv2, _⟩ := sealS_op (x := openS x) (z := z) rfl hv'
    refine ⟨hv2, ?_⟩
    rw [he2, he]
    exact .inr (.inl ⟨hs', hm', .inr rfl⟩)
  · obtain ⟨he, hv', hs'⟩ := sealS_op hs hv
    exact ⟨hv', he ▸ .inr (.inr ⟨hs', rfl⟩)⟩

/-- The update closure: reach a state by the store transitions (any at step 0). -/
def Cl (X : UPred RC) : UPred RC where
  holds n x := n = 0 ∨ ∃ y, ∃ hy : RC.Valid y, Reach x.val y ∧ X n ⟨y, hy⟩
  mono {n1 n2} {x1 x2} h hle hn := by
    have hle' : x1.val = x2.val := hle
    rcases h with h | ⟨y, hy, hr, hX⟩
    · exact .inl (by omega)
    · exact .inr ⟨y, hy, hle' ▸ hr, X.mono hX rfl hn⟩

noncomputable def CL : LM (UPred RC) where
  M := Cl
  ne := ⟨fun {n} P Q h m x hm hv => by
    show (m = 0 ∨ ∃ y, ∃ hy : RC.Valid y, Reach x y ∧ P m ⟨y, hy⟩) ↔
      (m = 0 ∨ ∃ y, ∃ hy : RC.Valid y, Reach x y ∧ Q m ⟨y, hy⟩)
    exact or_congr Iff.rfl (exists_congr fun y => exists_congr fun hy => and_congr Iff.rfl (h m y hm hy))⟩
  mono h := fun n x hx => by
    rcases hx with hx | ⟨y, hy, hr, hX⟩
    · exact .inl hx
    · exact .inr ⟨y, hy, hr, h n _ hX⟩
  intro := fun n x hx => .inr ⟨x.val, x.property, .inl rfl, hx⟩
  join := fun n x hx => by
    rcases hx with hx | ⟨y, hy, hr, hx⟩
    · exact .inl hx
    · rcases hx with hx | ⟨z, hz, hr2, hX⟩
      · exact .inl hx
      · exact .inr ⟨z, hz, hr.trans hr2, hX⟩
  frame := fun n x hx => by
    obtain ⟨x1, x2, H, h1, h2⟩ := hx
    rcases h1 with h1 | ⟨y, hy, hr, hX⟩
    · exact .inl h1
    · have H' : x1.op x2 = x.val := H
      have hv : (x1.op x2).Valid := H' ▸ x.property
      obtain ⟨hv', hr'⟩ := Reach_frame hr hv
      exact .inr ⟨y.op x2, hv', H' ▸ hr', y, x2, rfl, hX, h2⟩
  ex0 := fun n x hx => by
    rcases hx with hx | hx
    · left; cases n
      · rfl
      · exact hx.elim
    · exact hx


/-! ### Concrete resources -/

def f0 : RC := ⟨fun _ => .e, .f⟩
def o0 : RC := ⟨fun _ => .e, .o⟩
def d0 : RC := ⟨fun _ => .e, .d⟩
def t1 : RC := ⟨fun p => if p = 1 then .o else .e, .n⟩
def F1 : RC := ⟨fun p => if p = 1 then .o else .e, .f⟩
def D1 : RC := ⟨fun p => if p = 1 then .o else .e, .d⟩

theorem tokE_one : tokE {1} = t1 := RC.ext' (fun p => by
  by_cases h : p = 1
  · subst h; simp [tokE, t1, LawfulSet.mem_singleton]
  · simp [tokE, t1, h, LawfulSet.mem_singleton]) rfl

theorem tokE_empty : tokE ∅ = rcUnit := RC.ext' (fun p => by
  by_cases h : p ∈ (∅ : CoPset)
  · exact (CoPset.mem_empty h).elim
  · simp [tokE, rcUnit, h]) rfl

theorem f0t1 : f0.op t1 = F1 := RC.ext' (fun p => by by_cases h : p = 1 <;> simp [RC.op, f0, t1, F1, h, M2.op]) rfl
theorem d0t1 : d0.op t1 = D1 := RC.ext' (fun p => by by_cases h : p = 1 <;> simp [RC.op, d0, t1, D1, h, M2.op]) rfl
theorem t1d0 : t1.op d0 = D1 := by rw [RC.op_comm]; exact d0t1
theorem openF1 : openS F1 = o0 := RC.ext' (fun p => by by_cases h : p = 1 <;> simp [openS, F1, o0, h]) rfl
theorem sealo0 : sealS o0 = D1 := RC.ext' (fun p => by by_cases h : p = 1 <;> simp [sealS, o0, D1, h]) rfl

theorem f0_valid : f0.Valid := ⟨fun _ => by simp [f0], by simp [f0], by simp [f0]⟩
theorem o0_valid : o0.Valid := ⟨fun _ => by simp [o0], by simp [o0], fun _ => rfl⟩
theorem d0_valid : d0.Valid := ⟨fun _ => by simp [d0], by simp [d0], by simp [d0]⟩
theorem F1_valid : F1.Valid := ⟨fun p => by by_cases h : p = 1 <;> simp [F1, h], by simp [F1], by simp [F1]⟩
theorem D1_valid : D1.Valid := ⟨fun p => by by_cases h : p = 1 <;> simp [D1, h], by simp [D1], by simp [D1]⟩

theorem o0_op_s (z : RC) (h : (o0.op z).s = .f ∨ (o0.op z).s = .d) : False := by
  revert h; show (S5.o.op z.s = .f ∨ S5.o.op z.s = .d) → False
  cases z.s <;> simp [S5.op]

theorem t1_op_m1 (b : RC) (h : (t1.op b).m 1 = .e) : False := by
  revert h; show ((if (1 : Pos) = 1 then M2.o else M2.e).op (b.m 1) = .e) → False
  simp only [if_pos]; cases b.m 1 <;> simp [M2.op]

theorem t1_op_D1 (b : RC) (h : t1.op b = D1) : b = d0 := by
  have hm := fun p => congrArg (fun x => x.m p) h
  have hs := congrArg RC.s h
  refine RC.ext' (fun p => ?_) ?_
  · have := hm p
    by_cases hp : p = 1
    · subst hp
      revert this; simp only [RC.op, t1, D1, d0, if_pos]
      cases b.m 1 <;> simp [M2.op]
    · simpa [RC.op, t1, D1, d0, hp, M2.op] using this
  · revert hs; simp only [RC.op, t1, D1, d0]; cases b.s <;> simp [S5.op]

theorem Reach_d {x y : RC} (hs : x.s = .d) (h : Reach x y) : y = x := by
  rcases h with h | ⟨hs', _⟩ | ⟨hs', _⟩
  · exact h
  · rw [hs] at hs'; cases hs'
  · rw [hs] at hs'; cases hs'

theorem Reach_o {x y : RC} (hs : x.s = .o) (h : Reach x y) : y = x ∨ y = sealS x := by
  rcases h with h | ⟨hs', _⟩ | ⟨_, h⟩
  · exact .inl h
  · rw [hs] at hs'; cases hs'
  · exact .inr h

theorem Reach_F1 {y : RC} (h : Reach F1 y) : y = F1 ∨ y = o0 ∨ y = D1 := by
  rcases h with h | ⟨_, _, h | h⟩ | ⟨hs', _⟩
  · exact .inl h
  · exact .inr (.inl (h.trans openF1))
  · exact .inr (.inr (by rw [h, openF1, sealo0]))
  · simp [F1] at hs'

/-! ### The instance: P := emp ∨ own f₀ (persistent, not absorbing), Q := own f₀ ∨ own d₀, α := own o₀ -/

noncomputable def Pp : UPred RC := iprop(emp ∨ UPred.ownM f0)
noncomputable def Qq : UPred RC := iprop(UPred.ownM f0 ∨ UPred.ownM d0)

noncomputable def accC (X : UPred RC) : UPred RC :=
  wf CL {1} ∅ iprop(UPred.ownM o0 ∗ ((UPred.ownM o0 -∗ wf CL ∅ {1} X) ∧ (False -∗ wf CL ∅ {1} iprop(False))))

instance pers_Pp : Persistent Pp := ⟨fun _ _ _ => .inl rfl⟩

theorem PQ : iprop(Pp ∧ Qq) ⊢ UPred.ownM f0 := fun _ _ ⟨hp, hq⟩ => by
  rcases hq with hq | hq
  · exact hq
  · rcases hp with hp | hp
    · have : (UORA.unit : RC).s = d0.s := by rw [hp, hq]
      exact S5.noConfusion this
    · exact hp

/-- One round from the fresh store: open (f → o), abort seals (o → d), Q holds at d₀. -/
theorem posC : UPred.ownM f0 ⊢ accC Qq := by
  rintro n ⟨xv, hxv⟩ hx
  change f0 = xv at hx
  subst hx
  intro n' x' hn' H hown
  change tokE {1} = x' at hown
  subst hown
  rcases Nat.eq_zero_or_pos n' with h0 | h0
  · exact .inl h0
  refine .inr ⟨o0, o0_valid, ?_, ?_⟩
  · show Reach (f0.op (tokE {1})) o0
    rw [tokE_one, f0t1]; exact .inr (.inl ⟨rfl, by simp [F1], .inl openF1.symm⟩)
  · refine ⟨rcUnit, o0, RC.unit_op o0, ?_, o0, rcUnit, RC.op_unit o0, rfl, ?_, ?_⟩
    · show tokE ∅ = rcUnit; exact tokE_empty
    · intro m s hm Hs hs
      change o0 = s at hs; subst hs
      intro m' s' hm' Hs' hs'
      change tokE ∅ = s' at hs'; subst hs'
      rcases Nat.eq_zero_or_pos m' with h0 | h0
      · exact .inl h0
      refine .inr ⟨D1, D1_valid, ?_, tokE {1}, d0, ?_, rfl, .inr rfl⟩
      · show Reach ((rcUnit.op o0).op (tokE ∅)) D1
        rw [RC.unit_op, tokE_empty, RC.op_unit]; exact .inr (.inr ⟨rfl, sealo0.symm⟩)
      · show (tokE {1}).op d0 = D1; rw [tokE_one]; exact t1d0
    · intro m s hm Hs hf; exact hf.elim

/-- An accessor at the fresh store forces its continuation at the sealed remainder d₀. -/
theorem obs2 (X : UPred RC) (h : accC X 1 ⟨f0, f0_valid⟩) : X 1 ⟨d0, d0_valid⟩ := by
  have hv0 : RC.Valid (f0.op (tokE {1})) := by rw [tokE_one, f0t1]; exact F1_valid
  have h1 := h 1 (tokE {1}) (Nat.le_refl 1) hv0 rfl
  rcases h1 with h0 | ⟨y, hy, hr, x1, x2, H1, he, hb⟩
  · exact absurd h0 (by decide)
  change tokE ∅ = x1 at he; subst he
  have hr' : Reach F1 y := by
    have e : f0.op (tokE {1}) = F1 := by rw [tokE_one, f0t1]
    exact e ▸ hr
  have hx2 : x2 = y := by
    have e : (tokE ∅).op x2 = y := H1
    rwa [tokE_empty, RC.unit_op] at e
  subst hx2
  obtain ⟨z1, z2, H2, hO, hab, _⟩ := hb
  change o0 = z1 at hO; subst hO
  have H2' : o0.op z2 = x2 := H2
  rcases Reach_F1 hr' with rfl | rfl | rfl
  · exact (o0_op_s z2 (.inl (by rw [H2']; rfl))).elim
  · have hz : z2.op o0 = o0 := by rw [RC.op_comm]; exact H2'
    have hv1 : RC.Valid (z2.op o0) := by rw [hz]; exact o0_valid
    have h2 := hab 1 o0 (Nat.le_refl 1) hv1 rfl
    have hv2 : RC.Valid ((z2.op o0).op (tokE ∅)) := by rw [hz, tokE_empty, RC.op_unit]; exact o0_valid
    have h3 := h2 1 (tokE ∅) (Nat.le_refl 1) hv2 rfl
    rcases h3 with h0 | ⟨y', hy', hr2, a, b, H3, ha, hX⟩
    · exact absurd h0 (by decide)
    change tokE {1} = a at ha; subst ha
    have hr2' : Reach o0 y' := by
      have e : (z2.op o0).op (tokE ∅) = o0 := by rw [hz, tokE_empty, RC.op_unit]
      exact e ▸ hr2
    have H3' : t1.op b = y' := by rw [← tokE_one]; exact H3
    rcases Reach_o rfl hr2' with rfl | rfl
    · exact (t1_op_m1 b (by rw [H3']; rfl)).elim
    · rw [sealo0] at H3'
      have hb := t1_op_D1 b H3'
      subst hb
      exact hX
  · exact (o0_op_s z2 (.inr (by rw [H2']; rfl))).elim

/-- No accessor at the sealed store: nothing reachable carries the open token. -/
theorem obs1 (X : UPred RC) (h : accC X 1 ⟨d0, d0_valid⟩) : False := by
  have hv0 : RC.Valid (d0.op (tokE {1})) := by rw [tokE_one, d0t1]; exact D1_valid
  have h1 := h 1 (tokE {1}) (Nat.le_refl 1) hv0 rfl
  rcases h1 with h0 | ⟨y, hy, hr, x1, x2, H1, he, z1, z2, H2, hO, _⟩
  · exact absurd h0 (by decide)
  change tokE ∅ = x1 at he; subst he
  change o0 = z1 at hO; subst hO
  have hr' : Reach D1 y := by
    have e : d0.op (tokE {1}) = D1 := by rw [tokE_one, d0t1]
    exact e ▸ hr
  have hyD : y = D1 := Reach_d rfl hr'
  have hx2 : x2 = y := by
    have e : (tokE ∅).op x2 = y := H1
    rwa [tokE_empty, RC.unit_op] at e
  have H2' : o0.op z2 = D1 := by rw [← hyD, ← hx2]; exact H2
  exact o0_op_s z2 (.inr (by rw [H2']; rfl))

noncomputable def αC : Tele.Arg Tele.nil.{0} → UPred RC := fun _ => UPred.ownM o0
def βC : Tele.Arg Tele.nil.{0} → Tele.Arg Tele.nil.{0} → UPred RC := fun _ _ => iprop(False)

noncomputable abbrev AUc : UPred RC :=
  @atomic_update (UPred RC) _ (wFupd CL) Tele.nil.{0} Tele.nil.{0} {1} ∅ αC βC βC

theorem negC (H : iprop(Pp ∧ Qq) ⊢ AUc) : False := by
  letI : BIFUpdate (UPred RC) := wFupd CL
  have u : AUc ⊢ accC AUc := aupd_unfold.mp
  have h1 := u 1 ⟨f0, f0_valid⟩ (H 1 ⟨f0, f0_valid⟩ ⟨.inr rfl, .inl rfl⟩)
  exact obs1 _ (u 1 ⟨d0, d0_valid⟩ (obs2 _ h1))

-- `Iris.aupd_intro` idx 12: necessary
theorem t3c4_0 : ¬ drop0% Iris.aupd_intro 12 := fun h => by
  letI : BIFUpdate (UPred RC) := wFupd CL
  exact negC (@h (UPred RC) _ (wFupd CL) Tele.nil.{0} Tele.nil.{0} {1} ∅ Pp Qq αC βC βC pers_Pp (PQ.trans posC))

end T3c4
