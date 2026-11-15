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


namespace J3c0
open Iris Iris.BI

-- copies of T2c1 helpers (lnF, lcF, lcF', keepG): the Plain/Absorbing-free derivation of lc_fupd_elim_later_keep
theorem lnF {PROP : Type _} [Sbi PROP] : (iprop(True) : PROP) ⊢ iprop(∃ n, ▷^[n] (False : PROP)) :=
  loeb_weak (later_exists_false.trans (or_elim (exists_intro (Ψ := fun n => iprop(▷^[n] (False : PROP))) 1)
    (exists_elim fun n => exists_intro (Ψ := fun n => iprop(▷^[n] (False : PROP))) (n + 1))))

theorem lcF {PROP : Type _} [Sbi PROP] [BIFUpdate PROP] {lc : PROP}
    (helim : ∀ (E : CoPset) (P : PROP), lc ∗ ▷ P ⊢ |={E}=> P)
    (hkeep : ∀ {E : CoPset} (E' : CoPset) (Pi : Iris.SiProp) (R : PROP),
        (|={E,E'}=> <si_pure> Pi) ∧ (<si_pure> Pi ={E}=∗ R) ⊢ |={E}=> R) (E : CoPset) :
    ∀ n, iprop(lc ∗ ▷^[n] (False : PROP)) ⊢ |={E}=> (False : PROP)
  | 0 => (sep_mono_right (false_elim (P := iprop(lc -∗ |={E}=> (False : PROP))))).trans wand_elim_right
  | n + 1 => by
    have k : iprop(lc ∗ ▷ ▷^[n] (False : PROP)) ⊢ |={E}=> iprop(lc ∗ ▷^[n] (False : PROP)) := by
      iintro ⟨Hlc, HX⟩
      iapply (Iris.LaterCreditsPlain.lc_fupd_elim_later_keep helim hkeep (E := E) (P := iprop(▷^[n] (False : PROP)))) $$ Hlc HX
    exact k.trans ((BIFUpdate.mono (lcF helim hkeep E n)).trans BIFUpdate.trans)

theorem lcF' {PROP : Type _} [Sbi PROP] [BIFUpdate PROP] {lc : PROP}
    (helim : ∀ (E : CoPset) (P : PROP), lc ∗ ▷ P ⊢ |={E}=> P)
    (hkeep : ∀ {E : CoPset} (E' : CoPset) (Pi : Iris.SiProp) (R : PROP),
        (|={E,E'}=> <si_pure> Pi) ∧ (<si_pure> Pi ={E}=∗ R) ⊢ |={E}=> R) (E : CoPset) :
    lc ⊢ |={E}=> (False : PROP) :=
  (sep_emp.2.trans (sep_mono_right (true_intro.trans lnF))).trans
    (sep_exists_left.1.trans (exists_elim fun n => lcF helim hkeep E n))

theorem keepG {PROP : Type _} [Sbi PROP] [BIFUpdate PROP] {lc : PROP}
    (helim : ∀ (E : CoPset) (P : PROP), lc ∗ ▷ P ⊢ |={E}=> P)
    (hkeep : ∀ {E : CoPset} (E' : CoPset) (Pi : Iris.SiProp) (R : PROP),
        (|={E,E'}=> <si_pure> Pi) ∧ (<si_pure> Pi ={E}=∗ R) ⊢ |={E}=> R) {E : CoPset} {P : PROP} :
    ⊢ lc -∗ ▷ P ={E}=∗ lc ∗ P := by
  exact wand_intro (emp_sep.1.trans (wand_intro ((sep_mono_left (lcF' helim hkeep E)).trans
    (BIFUpdate.frame_right.trans (BIFUpdate.mono
      ((sep_mono_left (false_elim (P := iprop(▷ P -∗ lc ∗ P)))).trans wand_elim_left))))))

-- copy of T2c1 t2c1_8 (non-affine paradox for contradiction')
theorem c8 : drop% Iris.Inv.contradiction' 2 := by
  intro PROP _ fupd name inv _ hi hm hff hfr hmm ha hinv hc gname start fin _ hs hsf hns
  let F : PROP := fupd .M1 iprop(False)
  have fr : ∀ {E : Iris.Inv.Mask} {P Q : PROP}, iprop(fupd E P ∗ Q) ⊢ fupd E iprop(P ∗ Q) :=
    sep_comm.1.trans (hfr.trans (hm sep_comm.1))
  have fsep : ∀ {X : PROP}, iprop(False ∗ X) ⊢ (iprop(False) : PROP) :=
    (sep_mono_left false_elim).trans wand_elim_left
  have BF : iprop(<pers> F) ⊢ F :=
    ((and_intro .rfl .rfl).trans persistently_and_l).trans (fr.trans (hm fsep))
  have BB : iprop(<pers> F) ⊢ iprop(<pers> F ∗ <pers> F) := persistent_sep_dup_mp
  have L1 : ∀ γ i, iprop(fin γ ∗ inv i iprop(start γ ∨ <pers> F)) ⊢ F := fun γ i =>
    sep_comm.1.trans ((hinv (i := i) _ (fin γ) iprop(<pers> F) (sep_or_right.1.trans (or_elim
      ((hns γ).trans false_elim)
      ((persistently_absorb_l.trans (BB.trans (sep_mono_left or_intro_r))).trans hi)))).trans
      ((hm BF).trans hff))
  have L2 : ∀ γ i, iprop(fin γ ∗ inv i iprop(start γ ∨ <pers> F)) ⊢ iprop(<pers> F) := fun γ i =>
    persistently_intro.trans (persistently_mono (L1 γ i))
  have L3 : ∀ γ i, inv i iprop(start γ ∨ <pers> F) ⊢ fupd .M1 iprop(<pers> F) := fun γ i =>
    persistent_sep_dup_mp.trans (hinv _ _ iprop(<pers> F) (sep_or_right.1.trans (or_elim
      ((sep_mono_left (hsf γ)).trans (fr.trans (hm ((L2 γ i).trans (BB.trans (sep_mono_left or_intro_r))))))
      ((persistently_absorb_l.trans (BB.trans (sep_mono_left or_intro_r))).trans hi))))
  have G : ∀ γ, start γ ⊢ F := fun γ =>
    or_intro_l.trans ((ha _).trans ((hm (exists_elim fun i => L3 γ i)).trans (hff.trans ((hm BF).trans hff))))
  exact hc (hs.trans (hmm.trans ((hm (exists_elim G)).trans hff)))

-- copy of T2c1 t2c1_9 (non-affine paradox for contradiction)
theorem c9 : drop% Iris.Inv.contradiction 2 := by
  intro PROP _ fupd name inv _ hi hm hff hfr hmm ha hinv hc gname start fin hs hsf hns hdup
  let F : PROP := fupd .M1 iprop(False)
  let body : gname → PROP → PROP := fun γ P => iprop(start γ ∨ fin γ ∗ <pers> P)
  let sv : gname → PROP → PROP := fun γ P => iprop(∃ i, inv i (body γ P))
  let A : gname → PROP := fun γ => iprop(∃ P, <pers> (P -∗ F) ∗ sv γ P)
  have fr : ∀ {E : Iris.Inv.Mask} {P Q : PROP}, iprop(fupd E P ∗ Q) ⊢ fupd E iprop(P ∗ Q) :=
    sep_comm.1.trans (hfr.trans (hm sep_comm.1))
  have fsep : ∀ {X : PROP}, iprop(False ∗ X) ⊢ (iprop(False) : PROP) :=
    (sep_mono_left false_elim).trans wand_elim_left
  have FJ : ∀ {X : PROP}, fupd .M1 iprop(F ∗ X) ⊢ F := (hm fr).trans (hff.trans (hm fsep))
  have psplit : ∀ {X : PROP}, iprop(<pers> X) ⊢ iprop(X ∗ <pers> X) :=
    (and_intro .rfl .rfl).trans persistently_and_l
  -- opening the Q-invariant while holding fin
  have inner : ∀ γ Q j, iprop(inv j (body γ Q) ∗ fin γ) ⊢ fupd .M1 iprop(<pers> Q ∗ fin γ) := fun γ Q j =>
    hinv _ _ _ (sep_or_right.1.trans (or_elim ((hns γ).trans false_elim) (by
      refine Entails.trans ?_ hi
      iintro ⟨⟨Hf, HQ⟩, Hf2⟩
      icases (persistent_sep_dup_mp (P := iprop(<pers> Q))) $$ HQ with ⟨HQ, HQ'⟩
      isplitl [Hf HQ]
      · iright; isplitl [Hf]
        · iexact Hf
        · iexact HQ
      · isplitl [HQ']
        · iexact HQ'
        · iexact Hf2)))
  have W : ∀ γ P, iprop(body γ P ∗ <pers> P) ⊢ fupd .M0 iprop(fin γ ∗ <pers> P) := fun γ P =>
    sep_or_right.1.trans (or_elim ((sep_mono_left (hsf γ)).trans fr)
      ((sep_assoc.1.trans (sep_mono_right persistently_absorb_l)).trans hi))
  have outer : ∀ γ P Q i, iprop(inv i (body γ P) ∗ (sv γ Q ∗ <pers> P)) ⊢ fupd .M1 iprop(<pers> Q ∗ fin γ) :=
    fun γ P Q i => (hinv _ _ (fupd .M1 iprop(<pers> Q ∗ fin γ)) (by
      refine ((sep_mono_right sep_comm.1).trans sep_assoc.2).trans ?_
      refine (sep_mono_left (W γ P)).trans (fr.trans (hm ?_))
      refine (sep_mono_left (sep_mono_left (hdup γ))).trans ?_
      refine Entails.trans ?_ (sep_mono (or_intro_r (P := start γ)) (sep_exists_right.1.trans (exists_elim fun j => inner γ Q j)))
      iintro ⟨⟨⟨H1, H2⟩, H3⟩, H4⟩
      isplitl [H1 H3]
      · isplitl [H1]
        · iexact H1
        · iexact H3
      · isplitl [H4]
        · iexact H4
        · iexact H2)).trans hff
  have cast : ∀ γ P Q, iprop(sv γ P ∗ (sv γ Q ∗ <pers> P)) ⊢ fupd .M1 iprop(<pers> Q ∗ fin γ) := fun γ P Q =>
    sep_exists_right.1.trans (exists_elim fun i => outer γ P Q i)
  have pA : ∀ γ, A γ ⊢ iprop(<pers> A γ ∗ A γ) := fun γ =>
    persistent_sep_dup_mp.trans (sep_mono_left persistently_intro)
  have NA : ∀ γ, iprop(sv γ (A γ) ∗ A γ) ⊢ F := fun γ => by
    refine (sep_mono_right ((pA γ).trans sep_exists_left.1)).trans (sep_exists_left.1.trans (exists_elim fun P' => ?_))
    refine Entails.trans ?_ (FJ (X := iprop((<pers> P' ∗ fin γ) ∗ <pers> (P' -∗ F))))
    refine Entails.trans ?_ (hm (P := iprop((<pers> P' ∗ fin γ) ∗ <pers> (P' -∗ F)))
      (Q := iprop(F ∗ ((<pers> P' ∗ fin γ) ∗ <pers> (P' -∗ F)))) ?_)
    · refine Entails.trans ?_ fr
      refine Entails.trans ?_ (sep_mono_left (cast γ (A γ) P'))
      iintro ⟨Hs, HA, HN, HsP⟩
      isplitl [Hs HsP HA]
      · isplitl [Hs]
        · iexact Hs
        · isplitl [HsP]
          · iexact HsP
          · iexact HA
      · iexact HN
    · refine (sep_mono (sep_mono_left psplit) psplit).trans ?_
      iintro ⟨⟨⟨HP, HpP⟩, Hf⟩, ⟨HW, HN⟩⟩
      isplitl [HP HW]
      · iapply HW; iexact HP
      · isplitl [HpP Hf]
        · isplitl [HpP]
          · iexact HpP
          · iexact Hf
        · iexact HN
  have SA : ∀ γ, sv γ (A γ) ⊢ A γ := fun γ =>
    (persistent_sep_dup_mp.trans (sep_mono_left (persistently_intro.trans (persistently_mono (wand_intro (NA γ)))))).trans
      (exists_intro (Ψ := fun P => iprop(<pers> (P -∗ F) ∗ sv γ P)) (A γ))
  have G : ∀ γ, sv γ (A γ) ⊢ F := fun γ =>
    persistent_sep_dup_mp.trans ((sep_mono_right (SA γ)).trans (NA γ))
  have alloc : ∀ γ, start γ ⊢ fupd .M1 F := fun γ =>
    or_intro_l.trans ((ha (body γ (A γ))).trans (hm (G γ)))
  exact hc (hs.trans (hmm.trans ((hm (exists_elim fun γ => (alloc γ).trans hff)).trans hff)))

end J3c0

open Iris Iris.BI

namespace J3c0

-- `Iris.Inv.contradiction` idx 2, 7: jointly removable (run the non-affine paradox t2c1_9 with fupd' E P := fupd E (P ∗ True): fupd'_intro comes from sts_alloc, framing and mask_mono (the start token is absorbed into True), every other hypothesis carries over, and consistency transfers since False ∗ True ⊢ False)
theorem j3_1 : drop2% Iris.Inv.contradiction 2 7 := by
  intro PROP _ fupd name inv _ hm hff hfr hmm ha hinv hc gname start fin hs hsf hns hdup
  have fr : ∀ {E : Iris.Inv.Mask} {P Q : PROP}, iprop(fupd E P ∗ Q) ⊢ fupd E iprop(P ∗ Q) :=
    sep_comm.1.trans (hfr.trans (hm sep_comm.1))
  have addT : ∀ {X : PROP}, X ⊢ iprop(X ∗ True) := sep_emp.2.trans (sep_mono_right true_intro)
  have i0 : ∀ {P : PROP}, P ⊢ fupd .M0 iprop(P ∗ True) :=
    sep_emp.2.trans ((sep_mono_right hs).trans (hfr.trans (hm (sep_mono_right true_intro))))
  have hi' : ∀ {E : Iris.Inv.Mask} {P : PROP}, P ⊢ fupd E iprop(P ∗ True) := fun {E} {P} => by
    cases E
    · exact i0
    · exact i0.trans hmm
  have hm' : ∀ {E : Iris.Inv.Mask} {P Q : PROP}, (P ⊢ Q) → fupd E iprop(P ∗ True) ⊢ fupd E iprop(Q ∗ True) :=
    fun h => hm (sep_mono_left h)
  have hff' : ∀ {E : Iris.Inv.Mask} {P : PROP}, fupd E iprop(fupd E iprop(P ∗ True) ∗ True) ⊢ fupd E iprop(P ∗ True) :=
    (hm fr).trans (hff.trans (hm (sep_assoc.1.trans (sep_mono_right true_intro))))
  have hfr' : ∀ {E : Iris.Inv.Mask} {P Q : PROP}, iprop(P ∗ fupd E iprop(Q ∗ True)) ⊢ fupd E iprop((P ∗ Q) ∗ True) :=
    hfr.trans (hm sep_assoc.2)
  have hmm' : ∀ {P : PROP}, fupd .M0 iprop(P ∗ True) ⊢ fupd .M1 iprop(P ∗ True) := hmm
  have ha' : ∀ P : PROP, P ⊢ fupd .M1 iprop((∃ i, inv i P) ∗ True) := fun P => (ha P).trans (hm addT)
  have hinv' : ∀ {i : name} (P Q R : PROP), (iprop(P ∗ Q) ⊢ fupd .M0 iprop((P ∗ R) ∗ True)) →
      iprop(inv i P ∗ Q) ⊢ fupd .M1 iprop(R ∗ True) := fun P Q R h => hinv P Q iprop(R ∗ True) (h.trans (hm sep_assoc.1))
  have hc' : ¬(⊢ fupd .M1 iprop(False ∗ True)) := fun h =>
    hc (h.trans (hm ((sep_mono_left false_elim).trans wand_elim_left)))
  have hs' : ⊢ fupd .M0 iprop((∃ γ, start γ) ∗ True) := hs.trans (hm addT)
  have hsf' : ∀ γ, start γ ⊢ fupd .M0 iprop(fin γ ∗ True) := fun γ => (hsf γ).trans (hm addT)
  exact @c9 PROP _ (fun E P => fupd E iprop(P ∗ True)) name inv _ hi' hm' hff' hfr' hmm' ha' hinv' hc'
    gname start fin hs' hsf' hns hdup

-- `Iris.Inv.contradiction` idx 2, 11: jointly removable (mask_mono from inv_alloc True and inv_fupd without affinity (as in J2c0 j2_7), then the non-affine paradox t2c1_9)
theorem j3_2 : drop2% Iris.Inv.contradiction 2 11 := by
  intro PROP _ fupd name inv _ hi hm hff hfl hia hif hc gname start fin hs hsf hns hdup
  have hmm : ∀ {X : PROP}, fupd .M0 X ⊢ fupd .M1 X := fun {X} =>
    sep_emp.2.trans ((sep_mono_right (true_intro.trans (hia iprop(True)))).trans
      ((hfl).trans ((hm (sep_comm.1.trans <| sep_exists_right.1.trans (exists_elim fun i =>
        hif (i := i) iprop(True) (fupd .M0 X) X hfl))).trans hff)))
  exact @c9 PROP _ fupd name inv _ hi hm hff hfl hmm hia hif hc gname start fin hs hsf hns hdup

-- `Iris.Inv.contradiction'` idx 2, 7: jointly removable (run the non-affine paradox t2c1_8 with fupd' E P := fupd E (P ∗ True): fupd'_intro comes from sts_alloc, framing and mask_mono (the start token is absorbed into True), every other hypothesis carries over, and consistency transfers since False ∗ True ⊢ False)
theorem j3_3 : drop2% Iris.Inv.contradiction' 2 7 := by
  intro PROP _ fupd name inv _ hm hff hfr hmm ha hinv hc gname start fin _ hs hsf hns
  have fr : ∀ {E : Iris.Inv.Mask} {P Q : PROP}, iprop(fupd E P ∗ Q) ⊢ fupd E iprop(P ∗ Q) :=
    sep_comm.1.trans (hfr.trans (hm sep_comm.1))
  have addT : ∀ {X : PROP}, X ⊢ iprop(X ∗ True) := sep_emp.2.trans (sep_mono_right true_intro)
  have i0 : ∀ {P : PROP}, P ⊢ fupd .M0 iprop(P ∗ True) :=
    sep_emp.2.trans ((sep_mono_right hs).trans (hfr.trans (hm (sep_mono_right true_intro))))
  have hi' : ∀ {E : Iris.Inv.Mask} {P : PROP}, P ⊢ fupd E iprop(P ∗ True) := fun {E} {P} => by
    cases E
    · exact i0
    · exact i0.trans hmm
  have hm' : ∀ {E : Iris.Inv.Mask} {P Q : PROP}, (P ⊢ Q) → fupd E iprop(P ∗ True) ⊢ fupd E iprop(Q ∗ True) :=
    fun h => hm (sep_mono_left h)
  have hff' : ∀ {E : Iris.Inv.Mask} {P : PROP}, fupd E iprop(fupd E iprop(P ∗ True) ∗ True) ⊢ fupd E iprop(P ∗ True) :=
    (hm fr).trans (hff.trans (hm (sep_assoc.1.trans (sep_mono_right true_intro))))
  have hfr' : ∀ {E : Iris.Inv.Mask} {P Q : PROP}, iprop(P ∗ fupd E iprop(Q ∗ True)) ⊢ fupd E iprop((P ∗ Q) ∗ True) :=
    hfr.trans (hm sep_assoc.2)
  have hmm' : ∀ {P : PROP}, fupd .M0 iprop(P ∗ True) ⊢ fupd .M1 iprop(P ∗ True) := hmm
  have ha' : ∀ P : PROP, P ⊢ fupd .M1 iprop((∃ i, inv i P) ∗ True) := fun P => (ha P).trans (hm addT)
  have hinv' : ∀ {i : name} (P Q R : PROP), (iprop(P ∗ Q) ⊢ fupd .M0 iprop((P ∗ R) ∗ True)) →
      iprop(inv i P ∗ Q) ⊢ fupd .M1 iprop(R ∗ True) := fun P Q R h => hinv P Q iprop(R ∗ True) (h.trans (hm sep_assoc.1))
  have hc' : ¬(⊢ fupd .M1 iprop(False ∗ True)) := fun h =>
    hc (h.trans (hm ((sep_mono_left false_elim).trans wand_elim_left)))
  have hs' : ⊢ fupd .M0 iprop((∃ γ, start γ) ∗ True) := hs.trans (hm addT)
  have hsf' : ∀ γ, start γ ⊢ fupd .M0 iprop(fin γ ∗ True) := fun γ => (hsf γ).trans (hm addT)
  exact @c8 PROP _ (fun E P => fupd E iprop(P ∗ True)) name inv _ hi' hm' hff' hfr' hmm' ha' hinv' hc'
    gname start fin _ hs' hsf' hns

-- `Iris.Inv.contradiction'` idx 2, 11: jointly removable (mask_mono from inv_alloc True and inv_fupd without affinity (as in J2c0 j2_8), then the non-affine paradox t2c1_8)
theorem j3_4 : drop2% Iris.Inv.contradiction' 2 11 := by
  intro PROP _ fupd name inv _ hi hm hff hfl hia hif hc gname start fin _ hs hsf hns
  have hmm : ∀ {X : PROP}, fupd .M0 X ⊢ fupd .M1 X := fun {X} =>
    sep_emp.2.trans ((sep_mono_right (true_intro.trans (hia iprop(True)))).trans
      ((hfl).trans ((hm (sep_comm.1.trans <| sep_exists_right.1.trans (exists_elim fun i =>
        hif (i := i) iprop(True) (fupd .M0 X) X hfl))).trans hff)))
  exact @c8 PROP _ fupd name inv _ hi hm hff hfl hmm hia hif hc gname start fin _ hs hsf hns

-- `Iris.LaterCreditsPlain.lc_fupd_elim_later_keep` idx 8, 9: jointly removable (keepG uses neither instance: lc ⊢ fupd False from lc_fupd_elim_later and fupd_keep_si_pure' via Löb, then frame, for every P)
theorem j3_5 : drop2% Iris.LaterCreditsPlain.lc_fupd_elim_later_keep 8 9 := by
  intro PROP _ _ lc helim hkeep E P
  exact keepG helim hkeep

end J3c0
