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

namespace T3c5
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
theorem M2.op_bot {a b : M2} (h : a.op b ≠ .bot) : a ≠ .bot := by cases a <;> cases b <;> simp_all [M2.op]
theorem M2.op_e (a : M2) : a.op .e = a := by cases a <;> rfl

/-- RJ: exact mask tokens plus an idempotent junk bit `j` (b = junk only, b • b = b). -/
structure RJ where
  m : Pos → M2
  j : Bool

def RJ.op (x y : RJ) : RJ := ⟨fun p => (x.m p).op (y.m p), x.j || y.j⟩
def RJ.Valid (x : RJ) : Prop := ∀ p, x.m p ≠ .bot
def rjUnit : RJ := ⟨fun _ => .e, false⟩
def bJ : RJ := ⟨fun _ => .e, true⟩

theorem RJ.ext' {x y : RJ} (hm : ∀ p, x.m p = y.m p) (hj : x.j = y.j) : x = y := by
  cases x; cases y; simp only at hm hj; subst hj; congr; funext p; exact hm p

theorem RJ.op_assoc (x y z : RJ) : x.op (y.op z) = (x.op y).op z :=
  RJ.ext' (fun p => M2.op_assoc _ _ _) (by simp [RJ.op, Bool.or_assoc])
theorem RJ.op_comm (x y : RJ) : x.op y = y.op x :=
  RJ.ext' (fun p => M2.op_comm _ _) (by simp [RJ.op, Bool.or_comm])
theorem RJ.unit_op (x : RJ) : rjUnit.op x = x := RJ.ext' (fun _ => rfl) rfl
theorem RJ.op_unit (x : RJ) : x.op rjUnit = x := by rw [RJ.op_comm]; exact RJ.unit_op x

theorem RJ.valid_op_left {x y : RJ} (h : (x.op y).Valid) : x.Valid := fun p => M2.op_bot (h p)

theorem plus_valid {x : RJ} (h : x.Valid) : (x.op bJ).Valid := fun p => by
  show (x.m p).op .e ≠ .bot; rw [M2.op_e]; exact h p
theorem plus_plus (x : RJ) : (x.op bJ).op bJ = x.op bJ :=
  RJ.ext' (fun p => by show ((x.m p).op .e).op .e = (x.m p).op .e; rw [M2.op_e]) (by simp [RJ.op, bJ])
theorem plus_comm (x y : RJ) : (x.op bJ).op y = (x.op y).op bJ := by
  rw [← RJ.op_assoc, RJ.op_comm bJ y, RJ.op_assoc]

instance : OFE RJ := OFE.ofDiscrete RJ
instance : OFE.Discrete RJ := ⟨id⟩

instance rjORA : ORA RJ := ORA.ofDiscreteORAData {
  pcore := fun _ => some rjUnit
  op := RJ.op
  Valid := RJ.Valid
  Order := Eq
  assoc := RJ.op_assoc
  comm := RJ.op_comm
  pcore_op_left := by intro x cx h; cases h; exact RJ.unit_op x
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := fun _ _ h => RJ.valid_op_left h
  ord_trans := fun _ _ _ h1 h2 => h1.trans h2
  op_mono_left := by intro x y z h; cases h; rfl
  valid_of_ord := by intro x y h hv; cases h; exact hv
  pcore_mono := by intro x y cx h1 h2; exact ⟨rjUnit, rfl, by cases h2; rfl⟩
  pcore_order_op := by intro x cx h y; exact ⟨rjUnit, rfl, by cases h; rfl⟩
  pcore_increasing := by intro x cx h y; cases h; first | exact (RJ.unit_op y).symm | exact RJ.unit_op y
  increasing_closed := by intro x y _ h; cases h; assumption }

instance : OrderRefl RJ := ⟨fun x => show x = x from rfl⟩

instance rjUORA : UORA RJ where
  unit := rjUnit
  unit_valid := fun _ h => M2.noConfusion h
  unit_left_id := RJ.unit_op _
  pcore_unit := rfl

open Classical in
noncomputable def tokE (E : CoPset) : RJ := ⟨fun p => if p ∈ E then .o else .e, false⟩
noncomputable abbrev ownE (E : CoPset) : UPred RJ := UPred.ownM (tokE E)

theorem tokE_union {E1 E2 : CoPset} (h : E1 ## E2) : tokE (E1 ∪ E2) = (tokE E1).op (tokE E2) := by
  refine RJ.ext' (fun p => ?_) rfl
  simp only [tokE, RJ.op]
  have hu := (LawfulSet.mem_union (X := E1) (Y := E2) (x := p))
  have hd := h p
  by_cases h1 : p ∈ E1 <;> by_cases h2 : p ∈ E2 <;> simp_all [M2.op]

theorem tokE_diff {E1 E2 : CoPset} (h : E2 ⊆ E1) : tokE E1 = (tokE E2).op (tokE (E1 \ E2)) := by
  refine RJ.ext' (fun p => ?_) rfl
  simp only [tokE, RJ.op]
  have hu := (LawfulSet.mem_diff (X := E1) (Y := E2) (x := p))
  have hs := h p
  by_cases h1 : p ∈ E1 <;> by_cases h2 : p ∈ E2 <;> simp_all [M2.op]

theorem tokE_empty : tokE ∅ = rjUnit := RJ.ext' (fun p => by
  by_cases h : p ∈ (∅ : CoPset)
  · exact (CoPset.mem_empty h).elim
  · simp [tokE, rjUnit, h]) rfl

theorem ownM_disj (E1 E2 : CoPset) : UPred.ownM ((tokE E1).op (tokE E2)) ⊢ iprop(⌜E1 ## E2⌝) :=
  fun n x h p ⟨h1, h2⟩ => by
    have hv : RJ.Valid ((tokE E1).op (tokE E2)) := ORA.validN_of_ordN h x.property
    have := hv p
    simp [RJ.op, tokE, h1, h2, M2.op] at this

theorem ownE_join (E1 E2 : CoPset) : iprop(ownE E1 ∗ ownE E2) ⊢ iprop(⌜E1 ## E2⌝ ∧ ownE (E1 ∪ E2)) :=
  (UPred.ownM_op _ _).2.trans <| (and_intro (ownM_disj E1 E2) .rfl).trans <| pure_elim_left fun hd =>
    and_intro (pure_intro hd) (by show _ ⊢ UPred.ownM (tokE (E1 ∪ E2)); rw [tokE_union hd])

theorem ownE_split {E1 E2 : CoPset} (hd : E1 ## E2) : ownE (E1 ∪ E2) ⊢ iprop(ownE E1 ∗ ownE E2) := by
  show UPred.ownM (tokE (E1 ∪ E2)) ⊢ _; rw [tokE_union hd]; exact (UPred.ownM_op _ _).1

theorem ownE_sub {E1 E2 : CoPset} (h : E2 ⊆ E1) : ownE E1 ⊣⊢ iprop(ownE E2 ∗ ownE (E1 \ E2)) := by
  show UPred.ownM (tokE E1) ⊣⊢ _; rw [tokE_diff h]; exact UPred.ownM_op _ _

theorem ownE_empty : ownE ∅ ⊣⊢ (emp : UPred RJ) := by
  show UPred.ownM (tokE ∅) ⊣⊢ _; rw [tokE_empty]; exact .rfl

/-- Fancy update from mask ownership: own E1, get L (own E2 ∗ P). (T2c1's wf) -/
noncomputable def wf (L : LM (UPred RJ)) (E1 E2 : CoPset) (P : UPred RJ) : UPred RJ :=
  iprop(ownE E1 -∗ L.M iprop(ownE E2 ∗ P))

theorem pa {φ : Prop} {X Y Z : UPred RJ} (h : φ → iprop(X ∗ Y) ⊢ Z) : iprop((⌜φ⌝ ∧ X) ∗ Y) ⊢ Z :=
  (sep_mono_left (pure_elim_left fun hφ => wand_intro (h hφ))).trans wand_elim_left

theorem rcomm {A B C : UPred RJ} : iprop((A ∗ B) ∗ C) ⊢ iprop((A ∗ C) ∗ B) :=
  sep_assoc.1.trans ((sep_mono_right sep_comm.1).trans sep_assoc.2)

/-- Lawful for every closure modality L (T2c1's proof; it uses no affinity). -/
@[instance_reducible] noncomputable def wFupd (L : LM (UPred RJ)) : BIFUpdate (UPred RJ) where
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

/-! ### Astra's closure: M X holds at n ≥ 1 if X holds now, or at step 1 after adding the junk bit -/

def Cl (X : UPred RJ) : UPred RJ where
  holds n x := n = 0 ∨ X n x ∨ X 1 ⟨x.val.op bJ, plus_valid x.property⟩
  mono {n1 n2} {x1 x2} h hle hn := by
    have hle' : x1.val = x2.val := hle
    rcases h with h | h | h
    · exact .inl (by omega)
    · exact .inr (.inl (X.mono h hle hn))
    · exact .inr (.inr (X.mono h (show x1.val.op bJ = x2.val.op bJ by rw [hle']) (Nat.le_refl 1)))

noncomputable def CL : LM (UPred RJ) where
  M := Cl
  ne := ⟨fun {n} P Q h m x hm hv => by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exact ⟨fun _ => .inl h0, fun _ => .inl h0⟩
    · exact or_congr Iff.rfl (or_congr (h m x hm hv) (h 1 (x.op bJ) (by omega) (plus_valid hv)))⟩
  mono h := fun n x hx => by
    rcases hx with hx | hx | hx
    · exact .inl hx
    · exact .inr (.inl (h n _ hx))
    · exact .inr (.inr (h 1 _ hx))
  intro := fun n x hx => .inr (.inl hx)
  join := by
    intro P n x hx
    rcases hx with hx | hx | hx
    · exact .inl hx
    · exact hx
    · rcases hx with h1 | h1 | h1
      · exact (Nat.one_ne_zero h1).elim
      · exact .inr (.inr h1)
      · exact .inr (.inr (P.mono h1 (show (x.val.op bJ).op bJ = x.val.op bJ from plus_plus _) (Nat.le_refl 1)))
  frame := by
    intro P R n x hx
    obtain ⟨x1, x2, H, h1, h2⟩ := hx
    have H' : x1.op x2 = x.val := H
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exact .inl h0
    rcases h1 with h1 | h1 | h1
    · exact .inl h1
    · exact .inr (.inl ⟨x1, x2, H, h1, h2⟩)
    · refine .inr (.inr ⟨x1.op bJ, x2, ?_, h1, R.mono h2 rfl h0⟩)
      show (x1.op bJ).op x2 = x.val.op bJ
      rw [plus_comm, H']
  ex0 := by
    intro P n x hx
    rcases hx with hx | hx
    · left; cases n
      · rfl
      · exact hx.elim
    · exact hx

/-! ### The three BIFUpdateSbi laws -/

theorem wf_of_third {E1 E2 : CoPset} {X : UPred RJ} {n : Nat} {x : ValidAt RJ n}
    (h : ∀ (H : RJ.Valid (x.val.op (tokE E1))), 0 < n →
      (iprop(ownE E2 ∗ X) : UPred RJ) 1 ⟨(x.val.op (tokE E1)).op bJ, plus_valid H⟩) :
    wf CL E1 E2 X n x := by
  intro n' x' hn' H hown
  change tokE E1 = x' at hown
  subst hown
  rcases Nat.eq_zero_or_pos n' with h0 | h0
  · exact .inl h0
  · exact .inr (.inr (h H (by omega)))

theorem wf_elim {E1 E2 : CoPset} {X : UPred RJ} {n : Nat} {x : ValidAt RJ n}
    (h : wf CL E1 E2 X n x) (H : RJ.Valid (x.val.op (tokE E1))) :
    Cl (iprop(ownE E2 ∗ X)) n ⟨x.val.op (tokE E1), H⟩ :=
  h n (tokE E1) (Nat.le_refl n) H rfl

theorem Pi1_of {E : CoPset} {Pi : SiProp} {n : Nat} {y : ValidAt RJ n}
    (h : Cl (iprop(ownE E ∗ <si_pure> Pi)) n y) (hn : 0 < n) : Pi.holds 1 := by
  rcases h with h | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩
  · omega
  · exact Pi.closed h hn
  · exact h

theorem keepL (E E' : CoPset) (Pi : SiProp) (R : UPred RJ) :
    iprop(wf CL E E' iprop(<si_pure> Pi) ∧ (<si_pure> Pi -∗ wf CL E E R)) ⊢ wf CL E E R := by
  rintro n x ⟨h1, h2⟩
  apply wf_of_third
  intro H hn
  have hPi : Pi.holds 1 := Pi1_of (wf_elim h1 H) hn
  have hv1 : RJ.Valid (x.val.op bJ) := plus_valid x.property
  have h3 := h2 1 bJ hn hv1 hPi
  have hv2 : RJ.Valid ((x.val.op bJ).op (tokE E)) := by rw [plus_comm]; exact plus_valid H
  have h4 := wf_elim h3 hv2
  rcases h4 with h4 | h4 | h4
  · exact (Nat.one_ne_zero h4).elim
  · exact (iprop(ownE E ∗ R) : UPred RJ).mono h4
      (show (x.val.op bJ).op (tokE E) = (x.val.op (tokE E)).op bJ from plus_comm _ _) (Nat.le_refl 1)
  · exact (iprop(ownE E ∗ R) : UPred RJ).mono h4
      (show ((x.val.op bJ).op (tokE E)).op bJ = (x.val.op (tokE E)).op bJ by rw [plus_comm, plus_plus])
      (Nat.le_refl 1)

theorem split_t (x : RJ) (E : CoPset) : (tokE E).op (x.op bJ) = (x.op (tokE E)).op bJ := by
  rw [RJ.op_comm]; exact plus_comm _ _

theorem laterL (E : CoPset) (Pi : SiProp) :
    iprop(▷ wf CL E E iprop(<si_pure> Pi)) ⊢ wf CL E E iprop(▷ ◇ <si_pure> Pi) := by
  intro n x _
  apply wf_of_third
  intro H hn
  exact ⟨tokE E, x.val.op bJ, split_t x.val E, rfl, .inl trivial⟩

theorem sforallL (E : CoPset) (Ψi : SiProp → Prop) :
    iprop(∀ q, ⌜Ψi q⌝ → wf CL E E iprop(<si_pure> q)) ⊢ wf CL E E iprop(<si_pure> (sForall Ψi)) := by
  intro n x hx
  apply wf_of_third
  intro H hn
  refine ⟨tokE E, x.val.op bJ, split_t x.val E, rfl, ?_⟩
  intro q hq
  have hq' : (iprop(∀ q, ⌜Ψi q⌝ → wf CL E E iprop(<si_pure> q)) : UPred RJ) ⊢ wf CL E E iprop(<si_pure> q) :=
    (forall_elim q).trans (pure_imp_elim hq)
  exact Pi1_of (wf_elim (hq' n x hx) H) hn

theorem fsbi : @BIFUpdateSbi (UPred RJ) _ (wFupd CL) _ :=
  letI : BIFUpdate (UPred RJ) := wFupd CL
  { fupd_keep_siPure := fun {E} E' Pi R => keepL E E' Pi R
    fupd_siPure_later := fun E Pi => laterL E Pi
    fupd_siPure_sForall_2 := fun E Ψ => sforallL E Ψ }

theorem wfe (X : UPred RJ) : wf CL ∅ ∅ X ⊣⊢ Cl X :=
  ⟨sep_emp.2.trans <| (sep_mono_right ownE_empty.2).trans <| wand_elim_left.trans <|
      CL.mono ((sep_mono_left ownE_empty.1).trans emp_sep.1),
   wand_intro <| (sep_mono_right ownE_empty.1).trans <| sep_emp.1.trans <|
      CL.mono (emp_sep.2.trans (sep_mono_left ownE_empty.2))⟩

/-! ### Counterexamples (Astra): S₂ := ▷²False = <si_pure> {0,1} -/

def Pi2 : SiProp := ⟨fun n => n ≤ 1, fun h h2 => Nat.le_trans h2 h⟩
noncomputable abbrev S2 : UPred RJ := iprop(<si_pure> Pi2)
theorem unit_valid' : RJ.Valid rjUnit := fun _ h => M2.noConfusion h

/-- A: P = R := emp ∧ S₂; ■P = S₂ holds at step 1 after adding junk, but emp fails there. -/
noncomputable def PA : UPred RJ := iprop(emp ∧ S2)

theorem negA (H : iprop(Cl iprop(■ PA) ∧ (PA -∗ Cl PA)) ⊢ Cl PA) : False := by
  have h := H 2 ⟨rjUnit, unit_valid'⟩ ⟨.inr (.inr ⟨rfl, Nat.le_refl 1⟩), ?_⟩
  · rcases h with h | ⟨_, h⟩ | ⟨h, _⟩
    · exact absurd h (by decide)
    · exact absurd (show 2 ≤ 1 from h) (by decide)
    · have h' : rjUnit = rjUnit.op bJ := h
      have := congrArg RJ.j h'
      simp [rjUnit, bJ, RJ.op] at this
  · intro n' x' hn' Hv ⟨he, hs⟩
    change rjUnit = x' at he
    subst he
    exact .inr (.inl ⟨(RJ.unit_op _).symm, hs⟩)

/-- B: a owns name 1, c = a • b; P := S₂ ∧ (emp ∨ own c) is plain, R := S₂ ∧ own a. -/
def aJ : RJ := ⟨fun p => if p = 1 then .o else .e, false⟩
def cJ : RJ := aJ.op bJ
theorem aJ_valid : RJ.Valid aJ := fun p => by by_cases h : p = 1 <;> simp [aJ, h]

noncomputable def PB : UPred RJ := iprop(S2 ∧ (emp ∨ UPred.ownM cJ))
noncomputable def RB : UPred RJ := iprop(S2 ∧ UPred.ownM aJ)

instance plainPB : Plain PB := ⟨fun _ _ ⟨hs, _⟩ => ⟨hs, .inl rfl⟩⟩

theorem negB (H : iprop(Cl PB ∧ (PB -∗ Cl RB)) ⊢ Cl RB) : False := by
  have h := H 2 ⟨aJ, aJ_valid⟩ ⟨.inr (.inr ⟨Nat.le_refl 1, .inr rfl⟩), ?_⟩
  · rcases h with h | ⟨h, _⟩ | ⟨_, h⟩
    · exact absurd h (by decide)
    · exact absurd (show 2 ≤ 1 from h) (by decide)
    · have h' : aJ = aJ.op bJ := h
      have := congrArg RJ.j h'
      simp [aJ, bJ, RJ.op] at this
  · intro n' x' hn' Hv ⟨hs, he⟩
    rcases he with he | he
    · change rjUnit = x' at he
      subst he
      exact .inr (.inl ⟨hs, (RJ.op_unit aJ).symm⟩)
    · change cJ = x' at he
      subst he
      have hv : RJ.Valid (aJ.op cJ) := Hv
      have := hv 1
      simp [aJ, cJ, bJ, RJ.op, M2.op] at this

-- `Iris.fupd_keep_plainly` idx 4: necessary
theorem t3c5_0 : ¬ drop0% Iris.fupd_keep_plainly 4 := fun h => by
  letI : BIFUpdate (UPred RJ) := wFupd CL
  have h1 := @h (UPred RJ) _ (wFupd CL) fsbi ∅ ∅ ∅ PA PA
  exact negA ((and_mono (wfe _).2 (wand_mono_right (wfe _).2)).trans (h1.trans (wfe _).1))

-- `Iris.fupd_keep_plain` idx 4: necessary
theorem t3c5_1 : ¬ drop0% Iris.fupd_keep_plain 4 := fun h => by
  letI : BIFUpdate (UPred RJ) := wFupd CL
  have h1 := @h (UPred RJ) _ (wFupd CL) fsbi ∅ ∅ ∅ PB RB plainPB
  exact negB ((and_mono (wfe _).2 (wand_mono_right (wfe _).2)).trans (h1.trans (wfe _).1))

end T3c5
