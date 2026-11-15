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

namespace T3c2
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

/-- Token states per name: e (none), o (live token, exclusive), d (dead, duplicable), bot (invalid). -/
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

/-- MD: mask tokens that can die. -/
structure MD where
  g : Pos → T3

def MD.op (x y : MD) : MD := ⟨fun p => (x.g p).op (y.g p)⟩
def MD.Valid (x : MD) : Prop := ∀ p, x.g p ≠ .bot
def MD.Le (x y : MD) : Prop := ∃ zg : Pos → T3, ∀ p, y.g p = (x.g p).op (zg p)
def mdUnit : MD := ⟨fun _ => .e⟩

instance : OFE MD := OFE.ofDiscrete MD
instance : OFE.Discrete MD := ⟨id⟩

theorem MD.op_assoc (x y z : MD) : x.op (y.op z) = (x.op y).op z := by
  simp only [MD.op, T3.op_assoc]
theorem MD.op_comm (x y : MD) : x.op y = y.op x := by
  simp only [MD.op]; congr 1; funext p; exact T3.op_comm _ _
theorem MD.le_refl (x : MD) : x.Le x := ⟨fun _ => T3.e, fun p => (T3.op_e _).symm⟩
theorem MD.le_op (x z : MD) : z.Le (x.op z) := ⟨x.g, fun p => T3.op_comm _ _⟩
theorem MD.unit_op (x : MD) : mdUnit.op x = x := by cases x; simp only [MD.op, mdUnit, T3.e_op]

instance mdORA : ORA MD := ORA.ofDiscreteORAData {
  pcore := fun _ => some mdUnit
  op := MD.op
  Valid := MD.Valid
  Order := MD.Le
  assoc := MD.op_assoc
  comm := MD.op_comm
  pcore_op_left := by intro x cx h; cases h; exact MD.unit_op x
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := fun x y h p => T3.op_bot _ _ (h p)
  ord_trans := by
    rintro x y z ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨fun p => (a p).op (b p), fun p => by rw [hb, ha, T3.op_assoc]⟩
  op_mono_left := by
    rintro x y z ⟨a, ha⟩
    refine ⟨a, fun p => ?_⟩
    show ((y.g p).op (z.g p)) = ((x.g p).op (z.g p)).op (a p)
    rw [ha, ← T3.op_assoc, T3.op_comm (a p), T3.op_assoc]
  valid_of_ord := by
    rintro x y ⟨a, ha⟩ hv p
    exact T3.op_bot _ _ (by rw [← ha]; exact hv p)
  pcore_mono := by intro x y cx _ h; cases h; exact ⟨_, rfl, MD.le_refl _⟩
  pcore_order_op := by intro x cx h y; cases h; exact ⟨_, rfl, MD.le_refl _⟩
  pcore_increasing := by intro x cx h y; cases h; exact MD.le_op _ _
  increasing_closed := by intro x y _ _ z; exact MD.le_op _ _ }

instance : OrderRefl MD := ⟨MD.le_refl⟩

instance mdUORA : UORA MD where
  unit := mdUnit
  unit_valid := fun _ h => T3.noConfusion h
  unit_left_id := MD.unit_op _
  pcore_unit := rfl

instance : IncOrd MD := ⟨by rintro x y ⟨z, hz⟩; have hz' : y = x.op z := hz; subst hz'; exact ⟨z.g, fun _ => rfl⟩⟩

open Classical in
noncomputable def tokE (E : CoPset) : MD := ⟨fun p => if p ∈ E then .o else .e⟩
noncomputable abbrev ownE (E : CoPset) : UPred MD := UPred.ownM (tokE E)
open Classical in
noncomputable def deadAt (q : Pos) : MD := ⟨fun p => if p = q then .d else .e⟩
/-- Some token has died (semantic: some name is in state d). -/
def K : UPred MD where
  holds _ x := ∃ q, x.val.g q = .d
  mono {n1 n2} {x1 x2} h hle _ := by
    obtain ⟨q, hq⟩ := h
    obtain ⟨zg, hz⟩ := hle
    refine ⟨q, ?_⟩
    have hv : (x2.val.g q) ≠ .bot := x2.property q
    have hz' : x2.val.g q = (x1.val.g q).op (zg q) := hz q
    rw [hz', hq] at hv ⊢; cases h : zg q <;> simp_all [T3.op]

theorem tokE_union {E1 E2 : CoPset} (h : E1 ## E2) : tokE (E1 ∪ E2) = (tokE E1).op (tokE E2) := by
  simp only [tokE, MD.op]; congr 1; funext p
  have hu := (LawfulSet.mem_union (X := E1) (Y := E2) (x := p))
  have hd := h p
  by_cases h1 : p ∈ E1 <;> by_cases h2 : p ∈ E2 <;> simp_all [T3.op]

theorem tokE_diff {E1 E2 : CoPset} (h : E2 ⊆ E1) : tokE E1 = (tokE E2).op (tokE (E1 \ E2)) := by
  simp only [tokE, MD.op]; congr 1; funext p
  have hu := (LawfulSet.mem_diff (X := E1) (Y := E2) (x := p))
  have hs := h p
  by_cases h1 : p ∈ E1 <;> by_cases h2 : p ∈ E2 <;> simp_all [T3.op]

theorem ownM_disj (E1 E2 : CoPset) : UPred.ownM ((tokE E1).op (tokE E2)) ⊢ iprop(⌜E1 ## E2⌝) :=
  fun n x h p ⟨h1, h2⟩ => by
    have hv : MD.Valid ((tokE E1).op (tokE E2)) := ORA.validN_of_ordN h x.property
    have := hv p
    simp [MD.op, tokE, h1, h2, T3.op] at this

theorem ownE_join (E1 E2 : CoPset) : iprop(ownE E1 ∗ ownE E2) ⊢ iprop(⌜E1 ## E2⌝ ∧ ownE (E1 ∪ E2)) :=
  (UPred.ownM_op _ _).2.trans <| (and_intro (ownM_disj E1 E2) .rfl).trans <| pure_elim_left fun hd =>
    and_intro (pure_intro hd) (by show _ ⊢ UPred.ownM (tokE (E1 ∪ E2)); rw [tokE_union hd])

theorem ownE_split {E1 E2 : CoPset} (hd : E1 ## E2) : ownE (E1 ∪ E2) ⊢ iprop(ownE E1 ∗ ownE E2) := by
  show UPred.ownM (tokE (E1 ∪ E2)) ⊢ _; rw [tokE_union hd]; exact (UPred.ownM_op _ _).1

theorem ownE_sub {E1 E2 : CoPset} (h : E2 ⊆ E1) : ownE E1 ⊣⊢ iprop(ownE E2 ∗ ownE (E1 \ E2)) := by
  show UPred.ownM (tokE E1) ⊣⊢ _; rw [tokE_diff h]; exact UPred.ownM_op _ _

/-- Fancy update from mask ownership: own E1, get L (own E2 ∗ P). (T2c1's wf, on MD) -/
noncomputable def wf (L : LM (UPred MD)) (E1 E2 : CoPset) (P : UPred MD) : UPred MD :=
  iprop(ownE E1 -∗ L.M iprop(ownE E2 ∗ P))

theorem pa {φ : Prop} {X Y Z : UPred MD} (h : φ → iprop(X ∗ Y) ⊢ Z) : iprop((⌜φ⌝ ∧ X) ∗ Y) ⊢ Z :=
  (sep_mono_left (pure_elim_left fun hφ => wand_intro (h hφ))).trans wand_elim_left

theorem rcomm {A B C : UPred MD} : iprop((A ∗ B) ∗ C) ⊢ iprop((A ∗ C) ∗ B) :=
  sep_assoc.1.trans ((sep_mono_right sep_comm.1).trans sep_assoc.2)

/-- Lawful for every closure modality L (T2c1's proof). -/
@[instance_reducible] noncomputable def wFupd (L : LM (UPred MD)) : BIFUpdate (UPred MD) where
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

/-! ### The step drop Dr: read the argument at step 1. -/

def Dr (Q : UPred MD) : UPred MD where
  holds n x := n = 0 ∨ Q 1 ⟨x.val, x.property⟩
  mono {n1 n2} {x1 x2} h hle hn := by
    rcases Nat.eq_zero_or_pos n2 with h2 | h2
    · exact .inl h2
    · rcases h with h | h
      · omega
      · exact .inr (Q.mono h hle (Nat.le_refl 1))

theorem Dr_ne : OFE.NonExpansive Dr := ⟨fun {n} P Q h m x hm hv => by
  show (m = 0 ∨ P 1 ⟨x, hv⟩) ↔ (m = 0 ∨ Q 1 ⟨x, hv⟩)
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · simp [h0]
  · exact or_congr Iff.rfl (h 1 x (by omega) hv)⟩

theorem Dr_mono {P Q : UPred MD} (h : P ⊢ Q) : Dr P ⊢ Dr Q := fun n x hx => by
  rcases hx with hx | hx
  · exact .inl hx
  · exact .inr (h 1 _ hx)

theorem Dr_idem {P : UPred MD} : Dr (Dr P) ⊢ Dr P := fun n x hx => by
  rcases hx with hx | hx | hx
  · exact .inl hx
  · exact absurd hx (by decide)
  · exact .inr hx

theorem Dr_frame {P R : UPred MD} : iprop(Dr P ∗ R) ⊢ Dr iprop(P ∗ R) := fun n x hx => by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · exact .inl h0
  · obtain ⟨x1, x2, H, h1, h2⟩ := hx
    rcases h1 with h1 | h1
    · omega
    · exact .inr ⟨x1, x2, H, h1, R.mono h2 (MD.le_refl _) h0⟩

theorem Dr_bupd {P : UPred MD} : Dr iprop(|==> P) ⊢ iprop(|==> Dr P) := fun n x hx k yf hk hv => by
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · exact ⟨x.val, hv, .inl h0⟩
  · rcases hx with hx | hx
    · omega
    · obtain ⟨x', H, hx'⟩ := hx 1 yf (Nat.le_refl 1) hv
      exact ⟨x', H, .inr hx'⟩

theorem Dr_ex0 {P : UPred MD} : Dr iprop(◇ P) ⊢ Dr P := fun n x hx => by
  rcases hx with hx | hx | hx
  · exact .inl hx
  · exact hx.elim
  · exact .inr hx

/-- The closure: except0, or (after an update) the drop to step 1 together with a dead token. -/
noncomputable def DM (Q : UPred MD) : UPred MD := iprop(◇ Q ∨ |==> Dr iprop(Q ∗ K))

theorem K_dup : iprop(K ∗ K) ⊢ K := sep_elim_left

theorem DM_ex0 {P : UPred MD} : iprop(◇ DM P) ⊢ DM P :=
  or_elim (or_intro_l.trans or_intro_l) .rfl

theorem DM_frame {P R : UPred MD} : iprop(DM P ∗ R) ⊢ DM iprop(P ∗ R) :=
  sep_or_right.1.trans <| or_elim (except0_frame_right.trans or_intro_l)
    ((BIUpdate.frame_right.trans (BIUpdate.mono (Dr_frame.trans (Dr_mono rcomm)))).trans or_intro_r)

theorem Dr_or {A B : UPred MD} : Dr iprop(A ∨ B) ⊢ iprop(Dr A ∨ Dr B) := fun n x hx => by
  rcases hx with hx | hx | hx
  · exact .inl (.inl hx)
  · exact .inl (.inr hx)
  · exact .inr (.inr hx)

theorem DM_K {P : UPred MD} : iprop(DM P ∗ K) ⊢ iprop(◇ (P ∗ K) ∨ |==> Dr iprop(P ∗ K)) :=
  sep_or_right.1.trans <| or_mono except0_frame_right <|
    BIUpdate.frame_right.trans (BIUpdate.mono (Dr_frame.trans (Dr_mono (sep_assoc.1.trans (sep_mono_right K_dup)))))

theorem DM_join {P : UPred MD} : DM (DM P) ⊢ DM P :=
  or_elim DM_ex0 <| ((BIUpdate.mono ((Dr_mono DM_K).trans <| Dr_or.trans <|
    or_elim (Dr_ex0.trans BIUpdate.intro) (Dr_bupd.trans (BIUpdate.mono Dr_idem)))).trans BIUpdate.trans).trans or_intro_r

noncomputable def dL : LM (UPred MD) where
  M := DM
  ne := ⟨fun _ _ _ h => or_ne.ne (or_ne.ne .rfl h) (bupd_ne.ne (Dr_ne.ne (sep_ne.ne h .rfl)))⟩
  mono h := or_mono (except0_mono h) (BIUpdate.mono (Dr_mono (sep_mono_left h)))
  intro := except0_intro.trans or_intro_l
  join := DM_join
  frame := DM_frame
  ex0 := DM_ex0


/-! ### The refutation -/

def Pi2 : SiProp := ⟨fun n => n ≤ 1, fun h h2 => Nat.le_trans h2 h⟩
noncomputable abbrev X : UPred MD := iprop(<si_pure> Pi2)

def t1 : MD := ⟨fun p => if p = 1 then .o else .e⟩
def fo : MD := ⟨fun p => if p = 1 then .e else .o⟩
def kill1 (z : MD) : MD := ⟨fun p => if p = 1 then .d else z.g p⟩

theorem tokE_one : tokE {1} = t1 := by
  simp only [tokE, t1]; congr 1; funext p
  by_cases h : p = 1
  · subst h; simp [LawfulSet.mem_singleton]
  · simp [h, LawfulSet.mem_singleton]

theorem tokE_empty : tokE ∅ = mdUnit := by
  simp only [tokE, mdUnit]; congr 1; funext p
  by_cases h : p ∈ (∅ : CoPset)
  · exact (CoPset.mem_empty h).elim
  · simp [h]

def hasO (a : T3) : Prop := a = .o ∨ a = .bot
def hasD (a : T3) : Prop := a = .d ∨ a = .bot
theorem hasO_l {a b : T3} (h : hasO a) : hasO (a.op b) := by
  rcases h with rfl | rfl <;> cases b <;> simp [hasO, T3.op]
theorem hasO_r {a b : T3} (h : hasO b) : hasO (a.op b) := by rw [T3.op_comm]; exact hasO_l h
theorem hasD_l {a b : T3} (h : hasD a) : hasD (a.op b) := by
  rcases h with rfl | rfl <;> cases b <;> simp [hasD, T3.op]
theorem hasD_r {a b : T3} (h : hasD b) : hasD (a.op b) := by rw [T3.op_comm]; exact hasD_l h
theorem od {a b : T3} (ha : hasO a) (hb : hasD b) : a.op b = .bot := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rfl
theorem hasD_o {a : T3} (h : hasD a) : a.op .o = .bot := by rcases h with rfl | rfl <;> rfl
theorem bot_op (a : T3) : T3.bot.op a = .bot := by cases a <;> rfl

theorem le_g {a b : MD} (h : MD.Le a b) (p : Pos) : ∃ w, b.g p = (a.g p).op w :=
  let ⟨zg, hz⟩ := h; ⟨zg p, hz p⟩

theorem t3_open (a b c : T3) (h : (a.op (T3.o.op b)).op c ≠ .bot) : a.op (T3.o.op b) = .o ∧ c = .e := by
  cases a <;> cases b <;> cases c <;> simp_all [T3.op]

/-- Opening {1} to ∅ may kill token 1 and drop to step 1, so it proves anything that holds at step 1. -/
theorem pos (Y : UPred MD) (hY : ∀ x, Y 1 x) : (iprop(emp) : UPred MD) ⊢ wf dL {1} ∅ Y := by
  intro n x _ n' x' hn' H hown
  refine .inr ?_
  intro k yf hk hv
  have hown' : MD.Le t1 x' := tokE_one ▸ hown
  obtain ⟨zg, hz⟩ := hown'
  have hv' : ∀ p, (((x.val.op x').op yf).g p) ≠ .bot := hv
  have h1 := t3_open (x.val.g 1) (zg 1) (yf.g 1) (by
    have := hv' 1; have hz1 := hz 1; simp only [MD.op, t1, ite_true] at this hz1; rw [hz1] at this; simpa using this)
  refine ⟨kill1 (x.val.op x'), ?_, ?_⟩
  · show ∀ p, ((kill1 (x.val.op x')).op yf).g p ≠ .bot
    intro p
    by_cases hp : p = 1
    · subst hp; simp [kill1, MD.op, h1.2, T3.op]
    · have := hv' p; simpa [kill1, MD.op, hp] using this
  · rcases Nat.eq_zero_or_pos k with h0 | h0
    · exact .inl h0
    · refine .inr ⟨mdUnit, kill1 (x.val.op x'), by show MD.Le (mdUnit.op _) _; rw [MD.unit_op]; exact MD.le_refl _,
        ⟨mdUnit, mdUnit, ⟨fun _ => .e, fun p => rfl⟩, ?_, hY _⟩, ⟨1, by simp [kill1]⟩⟩
      show MD.Le (tokE ∅) mdUnit
      rw [tokE_empty]; exact MD.le_refl _

theorem fo_valid : MD.Valid (((UORA.unit : MD).op (tokE {1})).op fo) := fun p => by
  rw [show (UORA.unit : MD) = mdUnit from rfl, MD.unit_op, tokE_one]
  by_cases hp : p = 1 <;> simp [MD.op, t1, fo, hp, T3.op]

theorem u_valid : MD.Valid ((UORA.unit : MD).op (tokE {1})) := fun p => by
  rw [show (UORA.unit : MD) = mdUnit from rfl, MD.unit_op, tokE_one]
  by_cases hp : p = 1 <;> simp [t1, hp]

/-- Staying at {1} cannot drop the step: there is no spare token to kill. -/
theorem neg (Y : UPred MD)
    (hY : ∀ (y1 y2 : MD) (hv : ✓{2} y2), MD.Valid (y1.op y2) → MD.Le t1 y1 → Y 2 ⟨y2, hv⟩ → False) :
    ¬ ((iprop(emp) : UPred MD) ⊢ wf dL {1} {1} Y) := by
  intro h
  have h1 := h 2 ⟨UORA.unit, fun _ h => T3.noConfusion h⟩ (MD.le_refl _)
  have h2 := h1 2 (tokE {1}) (Nat.le_refl _) u_valid (MD.le_refl _)
  rcases h2 with (h2 | h2) | h2
  · exact h2
  · obtain ⟨y1, y2, H, hy1, hy2⟩ := h2
    have hv12 : MD.Valid (y1.op y2) := ORA.validN_of_ordN H u_valid
    exact hY y1 y2 _ hv12 (tokE_one ▸ hy1) hy2
  · obtain ⟨x'', H, hD⟩ := h2 2 fo (Nat.le_refl _) fo_valid
    have hH : ∀ p, ((x''.op fo).g p) ≠ .bot := H
    rcases hD with h0 | hD
    · exact absurd h0 (by decide)
    obtain ⟨y1, y2, H1, ⟨z1, z2, H2, hz1, _⟩, ⟨q, hq⟩⟩ := hD
    have hz1' : MD.Le t1 z1 := tokE_one ▸ hz1
    obtain ⟨w1, hw1⟩ := le_g hz1' 1
    obtain ⟨w2, hw2⟩ := le_g H2 1
    have hy1 : hasO (y1.g 1) := by
      have : y1.g 1 = (((t1.g 1).op w1).op (z2.g 1)).op w2 := by
        rw [← hw1]; exact hw2
      rw [this]; exact hasO_l (hasO_l (hasO_l (by simp [t1, hasO])))
    by_cases hq1 : q = 1
    · subst hq1
      obtain ⟨w3, hw3⟩ := le_g H1 1
      have := hH 1
      simp only [MD.op, fo, ite_true] at this
      have hx : x''.g 1 = .bot := by
        have : x''.g 1 = ((y1.g 1).op (y2.g 1)).op w3 := hw3
        rw [this, od hy1 (by rw [hq]; exact .inl rfl), bot_op]
      exact this (by rw [hx]; rfl)
    · obtain ⟨w3, hw3⟩ := le_g H1 q
      have := hH q
      have hx : hasD (x''.g q) := by
        have : x''.g q = ((y1.g q).op (y2.g q)).op w3 := hw3
        rw [this]; exact hasD_l (hasD_r (by rw [hq]; exact .inl rfl))
      simp only [MD.op, fo, hq1, ite_false] at this
      exact this (hasD_o hx)

theorem X_neg : ∀ (y1 y2 : MD) (hv : ✓{2} y2), MD.Valid (y1.op y2) → MD.Le t1 y1 → X 2 ⟨y2, hv⟩ → False :=
  fun _ _ _ _ _ h => by have : (2 : Nat) ≤ 1 := h; omega

theorem PX_neg : ∀ (y1 y2 : MD) (hv : ✓{2} y2), MD.Valid (y1.op y2) → MD.Le t1 y1 → iprop(■ X) 2 ⟨y2, hv⟩ → False :=
  fun _ _ _ _ _ h => by have : (2 : Nat) ≤ 1 := h; omega


theorem mp {A B : UPred MD} (h : (iprop(emp) : UPred MD) ⊢ iprop(A -∗ B)) (a : (iprop(emp) : UPred MD) ⊢ A) :
    (iprop(emp) : UPred MD) ⊢ B :=
  emp_sep.2.trans ((sep_mono h a).trans wand_elim_left)

theorem u11 : ({1} ∪ {1} : CoPset) = {1} :=
  CoPset.ext fun _ => ⟨fun h => (LawfulSet.mem_union.1 h).elim id id, fun h => LawfulSet.mem_union.2 (.inl h)⟩
theorem u01 : (∅ ∪ {1} : CoPset) = {1} :=
  CoPset.ext fun _ => ⟨fun h => (LawfulSet.mem_union.1 h).elim (fun h => (CoPset.mem_empty h).elim) id,
    fun h => LawfulSet.mem_union.2 (.inr h)⟩
theorem dj01 : (∅ : CoPset) ## {1} := fun _ ⟨h1, _⟩ => CoPset.mem_empty h1

theorem X1 : ∀ x, X 1 x := fun _ => (Nat.le_refl 1 : 1 ≤ 1)
theorem PX1 : ∀ x, iprop(■ X) 1 x := fun _ => (Nat.le_refl 1 : 1 ≤ 1)

theorem SY1 : ∀ x, iprop(▷ (wf dL ∅ {1} iprop(False))) 1 x := fun _ n' _ hn' _ _ => by
  have h0 : n' = 0 := Nat.eq_zero_of_le_zero hn'
  subst h0
  exact .inl (.inl trivial)

theorem SY_neg : ∀ (y1 y2 : MD) (hv : ✓{2} y2), MD.Valid (y1.op y2) → MD.Le t1 y1 →
    iprop(▷ (wf dL {1} {1} iprop(False))) 2 ⟨y2, hv⟩ → False := fun y1 y2 hv hval ht1 hy2 => by
  have hv21 : MD.Valid (y2.op y1) := MD.op_comm y1 y2 ▸ hval
  have r := hy2 1 y1 (Nat.le_refl 1) hv21 (show MD.Le (tokE {1}) y1 by rw [tokE_one]; exact ht1)
  rcases r with (r | ⟨_, _, _, _, hf⟩) | r
  · exact r
  · exact hf
  · have hvu : MD.Valid ((y2.op y1).op (UORA.unit : MD)) := by
      rw [MD.op_comm _ (UORA.unit : MD), show (UORA.unit : MD) = mdUnit from rfl, MD.unit_op]; exact hv21
    obtain ⟨_, _, hD⟩ := r 1 (UORA.unit : MD) (Nat.le_refl 1) hvu
    rcases hD with h0 | ⟨_, _, _, ⟨_, _, _, _, hf⟩, _⟩
    · omega
    · exact hf

-- `Iris.BIFUpdateSbi.fupd_keep_siPure` idx 4: necessary
theorem t3c2_0 : ¬ drop0% Iris.BIFUpdateSbi.fupd_keep_siPure 4 := fun h => by
  letI : BIFUpdate (UPred MD) := wFupd dL
  have h1 := @h (UPred MD) inferInstance (wFupd dL) inferInstance {1} ∅ Pi2 X
  exact neg X X_neg ((and_intro (pos X X1) (wand_intro (emp_sep.1.trans fupd_intro))).trans h1)

-- `Iris.fupd_keep_siPure` idx 3: necessary
theorem t3c2_1 : ¬ drop0% Iris.fupd_keep_siPure 3 := fun h => by
  letI : BIFUpdate (UPred MD) := wFupd dL
  have h1 := @h (UPred MD) _ (wFupd dL) {1} {1} ∅ Pi2 X
  exact neg X X_neg ((and_intro (pos X X1) (wand_intro (emp_sep.1.trans fupd_intro))).trans h1)

-- `Iris.fupd_keep_plainly` idx 3: necessary
theorem t3c2_2 : ¬ drop0% Iris.fupd_keep_plainly 3 := fun h => by
  letI : BIFUpdate (UPred MD) := wFupd dL
  have h1 := @h (UPred MD) _ (wFupd dL) _ {1} {1} ∅ X X
  exact neg X X_neg ((and_intro (pos iprop(■ X) PX1) (wand_intro (emp_sep.1.trans fupd_intro))).trans h1)

-- `Iris.fupd_keep_plain` idx 3: necessary
theorem t3c2_3 : ¬ drop0% Iris.fupd_keep_plain 3 := fun h => by
  letI : BIFUpdate (UPred MD) := wFupd dL
  have h1 := @h (UPred MD) _ (wFupd dL) _ {1} {1} ∅ X X _
  exact neg X X_neg ((and_intro (pos X X1) (wand_intro (emp_sep.1.trans fupd_intro))).trans h1)

-- `Iris.fupd_keep_plain_sep` idx 3: necessary
theorem t3c2_4 : ¬ drop0% Iris.fupd_keep_plain_sep 3 := fun h => by
  letI : BIFUpdate (UPred MD) := wFupd dL
  have h1 := @h (UPred MD) _ (wFupd dL) _ {1} ∅ X iprop(emp) _
  have a : (iprop(emp) : UPred MD) ⊢ iprop(emp -∗ wf dL {1} ∅ X) := wand_intro (emp_sep.1.trans (pos X X1))
  exact neg X X_neg ((mp (mp h1 a) .rfl).trans (BIFUpdate.mono sep_emp.1))

-- `Iris.fupd_plain_mask` idx 3: necessary
theorem t3c2_5 : ¬ drop0% Iris.fupd_plain_mask 3 := fun h => by
  letI : BIFUpdate (UPred MD) := wFupd dL
  have h1 := @h (UPred MD) _ (wFupd dL) _ {1} ∅ X _
  exact neg X X_neg ((pos X X1).trans h1)

-- `Iris.fupd_plainly_mask` idx 3: necessary
theorem t3c2_6 : ¬ drop0% Iris.fupd_plainly_mask 3 := fun h => by
  letI : BIFUpdate (UPred MD) := wFupd dL
  have h1 := @h (UPred MD) _ (wFupd dL) _ {1} ∅ X
  exact neg X X_neg ((pos iprop(■ X) PX1).trans h1)

-- `Iris.step_fupd_mask_frame_right` idx 7: necessary
theorem t3c2_7 : ¬ drop0% Iris.step_fupd_mask_frame_right 7 := fun h => by
  letI : BIFUpdate (UPred MD) := wFupd dL
  have h1 := @h (UPred MD) _ (wFupd dL) {1} ∅ {1} iprop(False) dj01
  rw [u11, u01] at h1
  exact neg _ SY_neg ((pos _ SY1).trans h1)

end T3c2
