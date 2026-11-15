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


namespace J2c0
open Iris Iris.BI

/-- SavedProp.contradiction from alloc, agree and consistency only (no persistence of saved, no bupd law):
with A' i := ∃ Q, ¬Q ∧ saved i Q, agreement gives saved i (A' i) ⊣⊢ False, so ∃ i, saved i (A' i) = False
(copy of the t1c2_16 argument, with the bupd_mono step replaced by rewriting along ⊣⊢). -/
theorem sp_contra2 {PROP : Type _} [BI PROP] (bupd : PROP → PROP) (ident : Type _) (saved : ident → PROP → PROP)
    (alloc : ∀ {P : ident → PROP}, ⊢ bupd iprop(∃ i, saved i (P i)))
    (hag : ∀ (i : ident) (P Q : PROP), saved i P ∧ saved i Q ⊢ □ (P ↔ Q))
    (cons : ¬(⊢ bupd iprop(False))) : False := by
  apply cons
  let A' : ident → PROP := fun i => iprop(∃ Q, ¬Q ∧ saved i Q)
  have hNA : ∀ i, iprop(saved i (A' i) ∧ A' i) ⊢ iprop(False) := fun i => by
    refine and_exists_left.1.trans (exists_elim fun Q => ?_)
    have h1 : iprop(saved i (A' i) ∧ (¬Q ∧ saved i Q)) ⊢ iprop(¬Q) := and_elim_r.trans and_elim_l
    have h2 : iprop(saved i (A' i) ∧ (¬Q ∧ saved i Q)) ⊢ A' i :=
      and_elim_r.trans (exists_intro (Ψ := fun Q => iprop(¬Q ∧ saved i Q)) Q)
    have h3 : iprop(saved i (A' i) ∧ (¬Q ∧ saved i Q)) ⊢ iprop(□ (Q ↔ A' i)) :=
      (and_intro (and_elim_r.trans and_elim_r) and_elim_l).trans (hag i Q (A' i))
    have h4 := (and_intro (h3.trans (intuitionistically_elim.trans and_elim_r)) h2).trans imp_elim_left
    exact (and_intro h1 h4).trans imp_elim_left
  have hS : ∀ i, saved i (A' i) ⊢ A' i := fun i =>
    (and_intro (imp_intro (hNA i)) .rfl).trans (exists_intro (Ψ := fun Q => iprop(¬Q ∧ saved i Q)) (A' i))
  have hF : iprop(∃ i, saved i (A' i)) ⊣⊢ iprop(False) :=
    ⟨exists_elim fun i => (and_intro .rfl (hS i)).trans (hNA i), false_elim⟩
  rw [← Iris.BI.BIBase.BiEntails.to_eq hF]
  exact alloc (P := A')

end J2c0

namespace J2c0
open Iris Iris.BI Iris.HeapLang Iris.Std Iris.ProgramLogic Language.Notation FromMathlib
open Iris.ProgramLogic.EctxLanguage Iris.ProgramLogic.EctxItemLanguage
/-- (copy of T1c3) -/
theorem irr_of_base {e : Exp} {σ : HeapLang.State} (hsub : SubredexesAreValues e)
    (hb : ∀ κ e' σ' efs, ¬ BaseStep e σ κ e' σ' efs) : PrimStep.Irreducible (e, σ) :=
  fun _ _ _ _ hp => hb _ _ _ _ (baseStep_of_primStep hp hsub)
-- copies of T1c3 helpers (adeqM, stuckM, var_irr, load0_irr, heapInv_default, goal_wp)
/-- `heap_adequacy` with the initial points-to and meta tokens handed to the program (any GF). -/
theorem adeqM {GF : BundledGFunctors} [HeapLangGpreS .hasLC GF] (e : Exp) (σ : HeapLang.State) (φ : Val → Prop)
    (Hwp : ∀ [HeapLangGS .hasLC GF], ⊢ iprop(BI.bigSepM (M := HeapF) (fun l v => pointsTo l (DFrac.own 1) v) σ.heap -∗
      BI.bigSepM (M := HeapF) (fun l _ => metaToken l ⊤) σ.heap -∗ WP e {{ v, ⌜φ v⌝ }})) :
    adequate .NotStuck e σ (fun v _ => φ v) := by
  refine wp_adequacy (GF := GF) .NotStuck e σ φ ?_
  intro inst κs
  imod genHeap_init (GF := GF) (H := HeapF) σ.heap with ⟨%γh, ⟨Hh, Hpts, Hmeta⟩⟩
  imod invHeap_init Loc _ (GF := GF) (H := HeapF) (E:= ⊤) with ⟨%γi, >Hi⟩
  imod (ProphMap.init κs σ.usedProphId) with ⟨%Gproph, Hproph⟩
  letI instHeapLangGS : HeapLangGS .hasLC GF := ⟨γh, Gproph, γi⟩
  imodintro
  iexists (fun σ κs => iprop% Iris.genHeapInterp σ.heap ∗ Iris.prophMapInterp κs σ.usedProphId)
  iexists (fun _ => iprop(True))
  simp only []
  ihave Hwp := (@Hwp _) $$ Hpts Hmeta
  iframe Hwp Hproph Hh
theorem stuckM {GF : BundledGFunctors} [HeapLangGpreS .hasLC GF] (e : Exp) (σ : HeapLang.State) (hv : toVal e = none)
    (hirr : PrimStep.Irreducible (e, σ))
    (Hwp : ∀ [HeapLangGS .hasLC GF], ⊢ iprop(BI.bigSepM (M := HeapF) (fun l v => pointsTo l (DFrac.own 1) v) σ.heap -∗
      BI.bigSepM (M := HeapF) (fun l _ => metaToken l ⊤) σ.heap -∗ WP e {{ _r, True }})) : False := by
  have had := adeqM (GF := GF) e σ (fun _ => True) Hwp
  rcases had.adequate_not_stuck [e] σ e rfl (.refl) (List.mem_singleton_self e) with h | ⟨obs, e', σ', efs, hs⟩
  · simp [hv] at h
  · exact hirr _ _ _ _ hs
theorem var_irr (σ : HeapLang.State) : PrimStep.Irreducible (Exp.var "a", σ) :=
  irr_of_base (subredexes_are_values fun Ki e' heq => by cases Ki <;> cases heq) (fun _ _ _ _ hb => by cases hb)
theorem load0_irr : PrimStep.Irreducible (Exp.load (.val (.lit (.loc ⟨0⟩))), (default : HeapLang.State)) :=
  irr_of_base (subredexes_are_values fun Ki e' heq => by cases Ki <;> cases heq <;> rfl)
    (fun _ _ _ _ hb => by cases hb; rename_i hg; simp [State.get?, default, get?_empty] at hg)
theorem heapInv_default {GF : BundledGFunctors} [HeapLangGS .hasLC GF] : ⊢ heapInv (GF := GF) (default : HeapLang.State) :=
  BI.sep_emp.2.trans (BI.sep_mono BigSepM.bigSepM_empty_intro BigSepS.bigSepS_empty_intro)
/-- Both disjuncts of `baseCompletenessGoal` for an expression without prim steps yield its WP (mask ⊤). -/
theorem goal_wp {GF : BundledGFunctors} [HeapLangGS .hasLC GF] (e : Exp) (σ : HeapLang.State)
    (hirr1 : PrimStep.Irreducible (e, σ)) (hirr0 : PrimStep.Irreducible (e, (default : HeapLang.State)))
    {Q : IProp GF} (H : Q ⊢ iprop(|={⊤}=> baseCompletenessGoal (GF := GF) e σ ⊤)) :
    Q ⊢ (iprop(WP e @ Stuckness.NotStuck; ⊤ {{ _r, True }}) : IProp GF) := by
  iintro HQ
  ihave H := H $$ HQ
  iapply (fupd_wp (GF := GF) (s := .NotStuck) (E := ⊤) (e := e) (Φ := fun _ => (iprop(True) : IProp GF)))
  imod H with (⟨_, H1⟩ | ⟨_, H2⟩)
  · imodintro; iapply H1
    inext; iintro %κ %v %σ' %efs %hs
    exact (hirr1 _ _ _ _ hs).elim
  · imodintro; iapply H2
    inext; iintro %e₂ %efs Ht
    imod Ht $$ %default [] with ⟨%κ, %σ', %hps, _⟩
    · iapply heapInv_default
    · cases hps with
      | once hs => exact (hirr0 _ _ _ _ hs).elim
      | next hs _ => exact (hirr0 _ _ _ _ hs).elim
-- copies of T1c3 helpers (pe_of_base, det2 and their lemmas)
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
/-- A HeapLang base step without effect in the empty state is a pure redex. -/
theorem pe_aux {e₁ e₂ : Exp} {σ σ' : HeapLang.State} {κ : List Observation} {efs : List Exp}
    (h0 : BaseStep e₁ σ κ e₂ σ' efs) (hσ : σ = default) (h1 : κ = []) (h2 : σ' = default) (h3 : efs = []) :
    Language.PureExec True 1 e₁ e₂ := by
  cases h0 with
  | recS f x e σ => exact instPureExecRec
  | pairS v1 v2 σ => exact instPureExecPair
  | injLS v σ => exact instPureExecInjl
  | injRS v σ => exact instPureExecInjr
  | betaS f x e1 v2 e' σ h => subst h; exact instPureExecBeta
  | unOpS op v v' σ h => exact ⟨fun _ => (instPureExecUnOp (op := op) (v := v) (v' := v')).pureExec h⟩
  | binOpS op v1 v2 v' σ h => exact ⟨fun _ => (instPureExecBinOp (op := op) (v1 := v1) (v2 := v2) (v' := v')).pureExec h⟩
  | ifTrueS e1 e2 σ => exact instPureExecIfTrue
  | ifFalseS e1 e2 σ => exact instPureExecIfFalse
  | fstS v1 v2 σ => exact instPureExecFst
  | sndS v1 v2 σ => exact instPureExecSnd
  | caseLS v e1 e2 σ => exact instPureExecCaseInjl
  | caseRS v e1 e2 σ => exact instPureExecCaseInjr
  | allocNS n v σ l hn hf => subst hσ; exact absurd h2 (alloc_ne l n (some v) hn)
  | freeS l v σ hl => subst hσ; simp [State.get?, default, get?_empty] at hl
  | loadS l v σ hl => subst hσ; simp [State.get?, default, get?_empty] at hl
  | storeS l v w σ hl => subst hσ; simp [State.get?, default, get?_empty] at hl
  | xchgS l v1 v2 σ hl => subst hσ; simp [State.get?, default, get?_empty] at hl
  | cmpXchgS l v1 v2 vl σ b hl _ _ => subst hσ; simp [State.get?, default, get?_empty] at hl
  | faaS l i1 i2 σ hl => subst hσ; simp [State.get?, default, get?_empty] at hl
  | forkS e σ => cases h3
  | newProphS σ p hp => subst hσ; exact absurd h2 (proph_ne p)
  | resolveS p v e σ w σ' κs ts hs hp => simp at h1
theorem pe_of_base {e₁ e₂ : Exp} (hb : ∀ σ : HeapLang.State, BaseStep e₁ σ [] e₂ σ []) :
    Language.PureExec True 1 e₁ e₂ := pe_aux (hb default) rfl rfl rfl rfl
theorem alloc_self_ne (σ : HeapLang.State) (l : Loc) (n : Int) (v : Option Val) (hn : 0 < n)
    (hf : σ.get? l = none) : σ.initHeap l n v ≠ σ := fun hσ => by
  have := congrArg (fun σ : HeapLang.State => σ.get? l) hσ
  simp only [State.get?] at this hf
  rw [get?_foldl_insert, ite_eq_left ⟨0, by omega, by simp [loc_add_zero]⟩, hf] at this
  cases this
theorem alloc_ne2 (σ : HeapLang.State) (la l : Loc) (n : Int) (v w : Option Val) (x : Val) (hn : 0 < n)
    (hla : σ.get? la = none) (hl : σ.get? l = some (some x)) : σ.initHeap la n v ≠ σ.initHeap l 1 w := fun hσ => by
  have := congrArg (fun σ : HeapLang.State => σ.get? la) hσ
  simp only [State.get?] at this hla hl
  rw [get?_foldl_insert, ite_eq_left ⟨0, by omega, by simp [loc_add_zero]⟩, get?_foldl_insert] at this
  split at this
  · rename_i hex
    obtain ⟨i, hi, rfl⟩ := hex
    have : i = 0 := by simp at hi; omega
    subst this; simp [loc_add_zero] at hla; rw [hla] at hl; cases hl
  · rw [hla] at this; cases this
/-- A base step that leaves the state alone (or rewrites one allocated cell) without observations
or forks is deterministic. -/
theorem det2 {e₁ e₂ e' : Exp} {σ σ0 σ2 : HeapLang.State} {κ : List Observation} {efs : List Exp}
    (h0 : BaseStep e₁ σ [] e₂ σ0 []) (hs : BaseStep e₁ σ κ e' σ2 efs)
    (hσ0 : σ0 = σ ∨ ∃ l x w, σ.get? l = some (some x) ∧ σ0 = σ.initHeap l 1 w) :
    κ = [] ∧ e' = e₂ ∧ σ2 = σ0 ∧ efs = [] := by
  generalize hk : ([] : List Observation) = k0 at h0
  generalize hf : ([] : List Exp) = f0 at h0
  cases h0 with
  | allocNS n v σ la hn hfr =>
    exfalso
    have hla : σ.get? la = none := by simpa [loc_add_zero] using hfr 0 (Int.le_refl 0) hn
    rcases hσ0 with h | ⟨l, x, w, hl, h⟩
    · exact alloc_self_ne σ la n (some v) hn hla h
    · exact alloc_ne2 σ la l n (some v) w x hn hla hl h
  | newProphS σ p hp =>
    exfalso
    rcases hσ0 with h | ⟨l, x, w, hl, h⟩
    · have := congrArg (fun s : HeapLang.State => s.usedProphId.contains p) h; simp_all
    · have h3 : σ.usedProphId.insert p = σ.usedProphId := congrArg State.usedProphId h
      have h2 : p ∈ σ.usedProphId.insert p := by simp
      rw [h3] at h2; simp_all
  | resolveS => simp at hk
  | forkS => simp at hf
  | _ => cases hs <;> simp_all
end J2c0

open Iris Iris.BI J2c0

namespace J2c0

-- `Iris.BI.only0_intuitionistically_mpr` idx 2, 3: jointly removable (only0_persistently_mpr plus the mpr half of only0_affinely; neither BILoeb nor Timeless emp is used)
theorem j2_1 : drop2% Iris.BI.only0_intuitionistically_mpr 2 3 := by
  intro PROP _ P
  exact (affinely_mono only0_persistently_mpr).trans (imp_intro ((and_intro (and_elim_l.trans affinely_elim_emp) ((and_mono_left affinely_elim).trans imp_elim_left)).trans .rfl))

section
open Iris.HeapLang Iris.Std Iris.ProgramLogic Language.Notation FromMathlib
-- `Iris.HeapLang.wp_base_atomic` idx 10, 13: jointly removable (hbase gives atomicity (a base step to a value) and determinism (det2: a base step that only rewrites one allocated cell is deterministic))
theorem j2_2 : drop2% Iris.HeapLang.wp_base_atomic 10 13 := by
  intro hlc GF inst e₁ v₂ l vlive vnew σ E hcell hbase
  exact Iris.HeapLang.wp_base_atomic l vlive vnew σ E
    (base_step_to_val_atomic .StronglyAtomic (hbase σ hcell)) hcell hbase
    (fun hg hs => det2 (hbase _ hg) hs (Or.inr ⟨l, vlive, vnew, hg, rfl⟩))

-- `Iris.HeapLang.wp_base_atomic_nochange` idx 9, 12: jointly removable (hbase gives atomicity (a base step to a value) and determinism (det2: a base step that leaves the state alone is deterministic))
theorem j2_3 : drop2% Iris.HeapLang.wp_base_atomic_nochange 9 12 := by
  intro hlc GF inst e₁ v₂ l vlive σ E hcell hbase
  exact Iris.HeapLang.wp_base_atomic_nochange l vlive σ E
    (base_step_to_val_atomic .StronglyAtomic (hbase σ hcell)) hcell hbase
    (fun hg hs => det2 (hbase _ hg) hs (Or.inl rfl))

-- `Iris.HeapLang.wp_base_pure` idx 6, 7: jointly removable (hbase alone: a state-free base step in every state is a PureExec True step, so instantiate φ := True)
theorem j2_4 : drop2% Iris.HeapLang.wp_base_pure 6 7 := by
  intro hlc GF inst e₁ e₂ φ σ E hbase
  exact @Iris.HeapLang.wp_base_pure hlc GF inst e₁ e₂ True (pe_of_base hbase) trivial σ E hbase

-- `Iris.HeapLang.wp_base_pure` idx 6, 10: not jointly removable (e₁ = e₂ = var "a" (stuck), φ = True: the WP of a stuck expression would be adequate)
theorem j2_5 : ¬ drop2_0% Iris.HeapLang.wp_base_pure 6 10 := fun h => by
  refine stuckM (GF := HeapLangS) (.var "a") default rfl (var_irr _) ?_
  intro inst; iintro - -
  iapply ((heapInv_default.trans (goal_wp (.var "a") default (var_irr _) (var_irr _)
    (@h .hasLC HeapLangS _ (.var "a") (.var "a") True trivial default ⊤))))
  all_goals first | itrivial | exact .rfl

-- `Iris.HeapLang.wp_base_pure` idx 7, 10: not jointly removable (e₁ = e₂ = var "a" (stuck), φ = False makes PureExec vacuous: the WP of a stuck expression would be adequate)
theorem j2_6 : ¬ drop2_0% Iris.HeapLang.wp_base_pure 7 10 := fun h => by
  refine stuckM (GF := HeapLangS) (.var "a") default rfl (var_irr _) ?_
  intro inst; iintro - -
  iapply ((heapInv_default.trans (goal_wp (.var "a") default (var_irr _) (var_irr _)
    (@h .hasLC HeapLangS _ (.var "a") (.var "a") False ⟨False.elim⟩ default ⊤))))
  all_goals first | itrivial | exact .rfl
end

-- `Iris.Inv.contradiction` idx 7, 11: jointly removable (mask_mono from inv_alloc True and inv_fupd (no fupd_intro used); then fupd_intro from sts_alloc, framing, mono and affinity at M0, mask_mono for M1)
theorem j2_7 : drop2% Iris.Inv.contradiction 7 11 := by
  intro PROP _ _ fupd name inv _ hm hff hfl hia hif hc gname start finished sa sf fns fd
  have hmm : ∀ {X : PROP}, fupd .M0 X ⊢ fupd .M1 X := fun {X} =>
    sep_emp.2.trans ((sep_mono_right (true_intro.trans (hia iprop(True)))).trans
      ((hfl).trans ((hm (sep_comm.1.trans <| sep_exists_right.1.trans (exists_elim fun i =>
        hif (i := i) iprop(True) (fupd .M0 X) X hfl))).trans hff)))
  have h0 : ∀ {X : PROP}, X ⊢ fupd .M0 X := fun {X} =>
    sep_emp.2.trans ((sep_mono_right sa).trans (hfl.trans (hm sep_elim_left)))
  refine Iris.Inv.contradiction fupd name inv ?_ hm hff hfl hmm hia hif hc gname start finished sa sf fns fd
  intro E X; cases E
  · exact h0
  · exact h0.trans hmm

-- `Iris.Inv.contradiction'` idx 7, 11: jointly removable (mask_mono from inv_alloc True and inv_fupd (no fupd_intro used); then fupd_intro from sts_alloc, framing, mono and affinity at M0, mask_mono for M1)
theorem j2_8 : drop2% Iris.Inv.contradiction' 7 11 := by
  intro PROP _ _ fupd name inv _ hm hff hfl hia hif hc gname start finished _ sa sf fns
  have hmm : ∀ {X : PROP}, fupd .M0 X ⊢ fupd .M1 X := fun {X} =>
    sep_emp.2.trans ((sep_mono_right (true_intro.trans (hia iprop(True)))).trans
      ((hfl).trans ((hm (sep_comm.1.trans <| sep_exists_right.1.trans (exists_elim fun i =>
        hif (i := i) iprop(True) (fupd .M0 X) X hfl))).trans hff)))
  have h0 : ∀ {X : PROP}, X ⊢ fupd .M0 X := fun {X} =>
    sep_emp.2.trans ((sep_mono_right sa).trans (hfl.trans (hm sep_elim_left)))
  refine Iris.Inv.contradiction' fupd name inv ?_ hm hff hfl hmm hia hif hc start finished sa sf fns
  intro E X; cases E
  · exact h0
  · exact h0.trans hmm

-- `Iris.SavedProp.contradiction` idx 2, 7: jointly removable (with A' i := ∃ Q, ¬Q ∧ saved i Q, agreement alone gives ∃ i, saved i (A' i) ⊣⊢ False, so alloc yields ⊢ bupd False against consistency; neither persistence of saved nor instPersExist is used)
theorem j2_9 : drop2% Iris.SavedProp.contradiction 2 7 := by
  intro PROP _ _ bupd ident saved _ _ _ _ alloc agree cons
  exact sp_contra2 bupd ident saved alloc agree cons

-- `Iris.SavedProp.contradiction` idx 3, 7: jointly removable (with A' i := ∃ Q, ¬Q ∧ saved i Q, agreement alone gives ∃ i, saved i (A' i) ⊣⊢ False, so alloc yields ⊢ bupd False against consistency; neither persistence of saved nor instAffine is used)
theorem j2_10 : drop2% Iris.SavedProp.contradiction 3 7 := by
  intro PROP _ _ bupd ident saved _ _ _ _ alloc agree cons
  exact sp_contra2 bupd ident saved alloc agree cons

-- `Iris.SavedProp.contradiction` idx 7, 8: jointly removable (with A' i := ∃ Q, ¬Q ∧ saved i Q, agreement alone gives ∃ i, saved i (A' i) ⊣⊢ False, so alloc yields ⊢ bupd False against consistency; neither persistence of saved nor bupd_intro is used)
theorem j2_11 : drop2% Iris.SavedProp.contradiction 7 8 := by
  intro PROP _ _ _ bupd ident saved _ _ _ alloc agree cons
  exact sp_contra2 bupd ident saved alloc agree cons

-- `Iris.SavedProp.contradiction` idx 7, 9: jointly removable (with A' i := ∃ Q, ¬Q ∧ saved i Q, agreement alone gives ∃ i, saved i (A' i) ⊣⊢ False, so alloc yields ⊢ bupd False against consistency; neither persistence of saved nor bupd_mono is used)
theorem j2_12 : drop2% Iris.SavedProp.contradiction 7 9 := by
  intro PROP _ _ _ bupd ident saved _ _ _ alloc agree cons
  exact sp_contra2 bupd ident saved alloc agree cons

-- `Iris.SavedProp.contradiction` idx 7, 10: jointly removable (with A' i := ∃ Q, ¬Q ∧ saved i Q, agreement alone gives ∃ i, saved i (A' i) ⊣⊢ False, so alloc yields ⊢ bupd False against consistency; neither persistence of saved nor bupd_trans is used)
theorem j2_13 : drop2% Iris.SavedProp.contradiction 7 10 := by
  intro PROP _ _ _ bupd ident saved _ _ _ alloc agree cons
  exact sp_contra2 bupd ident saved alloc agree cons

-- `Iris.SavedProp.contradiction` idx 7, 11: jointly removable (with A' i := ∃ Q, ¬Q ∧ saved i Q, agreement alone gives ∃ i, saved i (A' i) ⊣⊢ False, so alloc yields ⊢ bupd False against consistency; neither persistence of saved nor bupd_frame_right is used)
theorem j2_14 : drop2% Iris.SavedProp.contradiction 7 11 := by
  intro PROP _ _ _ bupd ident saved _ _ _ alloc agree cons
  exact sp_contra2 bupd ident saved alloc agree cons

open Std.DTreeMap.Internal in
-- `_private.Iris.Std.HeapInstances.0.Std.TreeMap.getElem?_mergeWith_eq_foldl` idx 3, 4: jointly removable (both sides are the same tree: mergeWith folds alter over the entries of t₂; no order laws needed)
theorem j2_15 : drop2% _private.Iris.Std.HeapInstances.«0».Std.TreeMap.getElem?_mergeWith_eq_foldl 3 4 := by
  intro K V _ t₁ t₂ f k
  show Impl.Const.get? (Impl.Const.mergeWith f t₁.inner.inner t₂.inner.inner t₁.inner.wf.balanced).impl k = Impl.Const.get? _ k
  rw [Impl.Const.mergeWith, Impl.foldl_eq_foldl]
  show _ = Impl.Const.get? (List.foldl _ t₁ (Impl.Const.toList t₂.inner.inner)).inner.inner k
  rw [Impl.Const.toList_eq_toListModel_map]
  generalize t₂.inner.inner.toListModel = L
  induction L generalizing t₁ with
  | nil => rfl
  | cons p tl ih =>
    rw [List.foldl_cons, List.map_cons, List.foldl_cons]
    refine Eq.trans ?_ (ih (t₁ := t₁.alter p.1 (Option.insertOrMerge (f p.1) p.2)))
    congr 3
    show Impl.BalancedTree.mk _ _ = Impl.BalancedTree.mk _ _
    congr 1
    show _ = (Impl.Const.alter p.1 _ t₁.inner.inner _).impl
    congr 2; funext o; cases o <;> rfl

end J2c0
