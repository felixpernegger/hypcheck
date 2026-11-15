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

namespace W6c2
open Iris Iris.HeapLang Iris.Std
abbrev vbad : Val := .rec_ .anon .anon (.var "b")
theorem vbad_nc : vbad.isClosed = false := by decide
theorem va_nc : (Exp.var "a").isClosed ∅ = false := by decide
abbrev σbad : HeapLang.State := { heap := Iris.Std.insert (M := HeapF) ∅ ⟨0⟩ (some vbad), usedProphId := ∅ }
abbrev sgA : VarMapF Val := Iris.Std.insert (∅ : VarMapF Val) "a" (.lit .unit)
end W6c2

namespace W6c2
open Iris Iris.BI Iris.HeapLang Iris.Std Iris.ProgramLogic Language.Notation FromMathlib
open Iris.ProgramLogic.EctxLanguage Iris.ProgramLogic.EctxItemLanguage
theorem adeqP (e : Exp) (σ : HeapLang.State) (φ : Val → Prop)
    (Hwp : ∀ [HeapLangGS .hasLC HeapLangS], ⊢ iprop(BI.bigSepM (M := HeapF) (fun l v => pointsTo l (DFrac.own 1) v) σ.heap -∗ WP e {{ v, ⌜φ v⌝ }})) :
    adequate .NotStuck e σ (fun v _ => φ v) := by
  refine wp_adequacy (GF := HeapLangS) .NotStuck e σ φ ?_
  intro inst κs
  imod genHeap_init (GF := HeapLangS) (H := HeapF) σ.heap with ⟨%γh, ⟨Hh, Hpts, _⟩⟩
  imod invHeap_init Loc _ (GF := HeapLangS) (H := HeapF) (E:= ⊤) with ⟨%γi, >Hi⟩
  imod (ProphMap.init κs σ.usedProphId) with ⟨%Gproph, Hproph⟩
  letI instHeapLangGS : HeapLangGS .hasLC HeapLangS := ⟨γh, Gproph, γi⟩
  imodintro
  iexists (fun σ κs => iprop% Iris.genHeapInterp σ.heap ∗ Iris.prophMapInterp κs σ.usedProphId)
  iexists (fun _ => iprop(True))
  simp only []
  ihave Hwp := (@Hwp _) $$ Hpts
  iframe Hwp Hproph Hh
/-- A HeapLang configuration that is not a value and has no prim step cannot have a safe WP. -/
theorem stuck_false (e : Exp) (σ : HeapLang.State) (hv : toVal e = none)
    (hirr : PrimStep.Irreducible (e, σ))
    (Hwp : ∀ [HeapLangGS .hasLC HeapLangS], ⊢ iprop(BI.bigSepM (M := HeapF) (fun l v => pointsTo l (DFrac.own 1) v) σ.heap -∗ WP e {{ _r, True }})) :
    False := by
  have had := adeqP e σ (fun _ => True) Hwp
  have hns := had.adequate_not_stuck [e] σ e rfl (.refl) (List.mem_singleton_self e)
  rcases hns with h | ⟨obs, e', σ', efs, hs⟩
  · simp [hv] at h
  · exact hirr _ _ _ _ hs
/-- A configuration that steps (purely, without forks) to a value `w ≠ v` refutes `WP e {{ r, r = v }}`. -/
theorem wrong_val (e : Exp) (σ σ' : HeapLang.State) (κ : List Observation) (w v : Val)
    (hstep : PrimStep.primStep (e, σ) κ (Exp.val w, σ', [])) (hne : w ≠ v)
    (Hwp : ∀ [HeapLangGS .hasLC HeapLangS], ⊢ iprop(BI.bigSepM (M := HeapF) (fun l v => pointsTo l (DFrac.own 1) v) σ.heap -∗ WP e {{ r, ⌜r = v⌝ }})) :
    False := by
  have had := adeqP e σ (fun r => r = v) Hwp
  exact hne (had.adequate_result [] σ' w (.tail .refl ⟨κ, .of_primStep hstep (t₁ := []) (t₂ := [])⟩))
end W6c2

namespace W6c2
open Iris Iris.BI Iris.HeapLang Iris.Std Iris.ProgramLogic Language.Notation FromMathlib
open Iris.ProgramLogic.EctxLanguage Iris.ProgramLogic.EctxItemLanguage
abbrev vU : Val := .lit .unit
abbrev vZ : Val := .lit (.int 0)
abbrev vO : Val := .lit (.int 1)
/-- A boxed value: `compareSafe vP vP = false`. -/
abbrev vP : Val := .pair vU vU
abbrev vQ : Val := .pair vU vZ
/-- One heap cell `⟨0⟩ ↦ v`. -/
abbrev σ1 (v : Val) : HeapLang.State :=
  { heap := PartialMap.singleton (M := HeapF) ⟨0⟩ (some v), usedProphId := ∅ }
theorem σ1_get (v : Val) : (σ1 v).get? ((⟨0⟩ : Loc) + ((0 : Nat) : Int)) = some (some v) := by
  simp [State.get?, PartialMap.singleton, LawfulPartialMap.get?_insert, loc_add_zero]
theorem irr_of_base {e : Exp} {σ : HeapLang.State} (hsub : SubredexesAreValues e)
    (hb : ∀ κ e' σ' efs, ¬ BaseStep e σ κ e' σ' efs) : PrimStep.Irreducible (e, σ) :=
  fun _ _ _ _ hp => hb _ _ _ _ (baseStep_of_primStep hp hsub)
theorem pts1 [HeapLangGS .hasLC HeapLangS] (v : Val) :
    BI.bigSepM (M := HeapF) (fun l v => pointsTo l (DFrac.own 1) v) (σ1 v).heap ⊢ pointsTo (⟨0⟩ : Loc) (DFrac.own 1) (some v) :=
  BI.BigSepM.bigSepM_singleton.1
theorem σ1_get0 (v : Val) : (σ1 v).get? (⟨0⟩ : Loc) = some (some v) := by
  simp [State.get?, PartialMap.singleton, LawfulPartialMap.get?_insert]
/-- `cmpXchg` on the cell `L ↦ vl` is stuck when `vl` and `v1` cannot be compared safely. -/
theorem cx_unsafe_irr' (L : Loc) (vl v1 v2 : Val) (hL : (σ1 vl).get? L = some (some vl)) (hs : vl.compareSafe v1 = false) :
    PrimStep.Irreducible (Exp.cmpXchg (.val (.lit (.loc L))) (.val v1) (.val v2), σ1 vl) :=
  irr_of_base (subredexes_are_values fun Ki e' heq => by cases Ki <;> cases heq <;> rfl)
    (fun _ _ _ _ hb => by
      cases hb with
      | cmpXchgS _ _ _ vl' _ _ hg hsafe _ =>
        rw [hL] at hg; cases hg; simp_all)
theorem cx_unsafe_irr (vl v1 v2 : Val) (hs : vl.compareSafe v1 = false) :
    PrimStep.Irreducible (Exp.cmpXchg (.val (.lit (.loc ((⟨0⟩:Loc) + ((0:Nat):Int))))) (.val v1) (.val v2), σ1 vl) :=
  irr_of_base (subredexes_are_values fun Ki e' heq => by cases Ki <;> cases heq <;> rfl)
    (fun _ _ _ _ hb => by
      cases hb with
      | cmpXchgS _ _ _ vl' _ _ hg hsafe _ =>
        rw [σ1_get] at hg; cases hg; simp_all)
theorem var_irr (σ : HeapLang.State) : PrimStep.Irreducible (Exp.var "a", σ) :=
  irr_of_base (subredexes_are_values fun Ki e' heq => by cases Ki <;> cases heq) (fun _ _ _ _ hb => by cases hb)
/-- Soundness shortcut: an `IProp HeapLangS` proof of `False` under every `HeapLangGS` instance is impossible. -/
theorem false_of (H : ∀ [HeapLangGS .hasLC HeapLangS], ⊢ (iprop(False) : IProp HeapLangS)) : False :=
  stuck_false (.var "a") default rfl (var_irr _) (fun {_} => H.trans BI.false_elim)
/-- Two full points-to of the same cell with different values give `False`. -/
theorem pt_twice_false [HeapLangGS .hasLC HeapLangS] (L : Loc) (A : ∀ v : Val, ⊢ pointsTo L (DFrac.own 1) (some v)) :
    ⊢ (iprop(False) : IProp HeapLangS) := by
  exact (BI.emp_sep.2.trans (BI.sep_mono (A vU) (A vZ))).trans
    (pointsTo_agree.trans (BI.pure_elim' fun h => absurd h (by decide)))
theorem arr1v [HeapLangGS .hasLC HeapLangS] (v : Val) :
    pointsTo (⟨0⟩:Loc) (DFrac.own 1) (some v) ⊢ array (⟨0⟩:Loc) (DFrac.own 1) (#v[v]).toList := array_singleton.2
end W6c2

namespace W6c2
open Iris Iris.HeapLang Iris.Std Iris.ProgramLogic Iris.ProgramLogic.Language Iris.ProgramLogic.EctxLanguage Iris.ProgramLogic.EctxItemLanguage FromMathlib
abbrev E1 : Exp := .if (.val (.lit (.bool true))) (.var "a") (.var "a")
abbrev σp : HeapLang.State := { heap := ∅, usedProphId := {⟨0⟩} }
theorem e1_step (σ : HeapLang.State) : BaseStep E1 σ [] (.var "a") σ [] := .ifTrueS _ _ σ
theorem e1_fill (Ki : ECtxItem) (e : Exp) (h : E1 = Ki.fill e) : e = .val (.lit (.bool true)) := by
  cases Ki <;> simp [ECtxItem.fill] at h
  exact h.1.symm
theorem res_E1_irred (σ : HeapLang.State) (v1 v2 : Val) :
    PrimStep.Irreducible (Exp.resolve E1 (.val v1) (.val v2), σ) := by
  intro obs e' σ' eₜ hstep
  generalize hsrc : Exp.resolve E1 (.val v1) (.val v2) = src at hstep
  obtain ⟨Hbase⟩ := hstep
  rename_i e₁' e₂' K
  cases K using List.reverseRec with
  | nil =>
    simp only [fill_nil] at hsrc; subst hsrc
    cases Hbase with | resolveS _ _ _ _ _ _ _ _ hb _ => cases hb
  | append_singleton K' Ki =>
    cases Ki <;>
      simp only [fill_append, fill_cons, fill_nil, fillItem, ECtxItem.fill,
        Exp.resolve.injEq, reduceCtorEq] at hsrc
    case resolveL => exact baseStep_fill_eq_val_absurd Hbase (e1_fill _ _ hsrc.1).symm
    case resolveM => exact baseStep_fill_eq_val_absurd Hbase hsrc.2.1
    case resolveR => exact baseStep_fill_eq_val_absurd Hbase hsrc.2.2
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
end W6c2

namespace W6c2
open Iris Iris.BI Iris.HeapLang Iris.Std Iris.ProgramLogic Language.Notation FromMathlib
open Iris.ProgramLogic.EctxLanguage Iris.ProgramLogic.EctxItemLanguage
theorem fill_var_absurd {K : List ECtxItem} {e e' : Exp} {σ σ' : HeapLang.State} {κ : List Observation} {efs : List Exp}
    (hb : BaseStep e σ κ e' σ' efs) (h : Exp.var "a" = fill K e) : False := by
  cases K using List.reverseRec with
  | nil => simp only [fill_nil] at h; subst h; cases hb
  | append_singleton K' Ki =>
    cases Ki <;> simp only [fill_append, fill_cons, fill_nil, fillItem, ECtxItem.fill, reduceCtorEq] at h
/-- `cmpXchg` with a free variable as one of its value arguments is stuck. -/
theorem cx_var_irr (L : Loc) (a b : Exp) (σ : HeapLang.State)
    (hab : (a = .var "a" ∧ ∃ v, b = .val v) ∨ (∃ v, a = .val v) ∧ b = .var "a") :
    PrimStep.Irreducible (Exp.cmpXchg (.val (.lit (.loc L))) a b, σ) := by
  intro obs e' σ' eₜ hstep
  generalize hsrc : Exp.cmpXchg (.val (.lit (.loc L))) a b = src at hstep
  obtain ⟨Hbase⟩ := hstep
  rename_i e₁' e₂' K
  cases K using List.reverseRec with
  | nil =>
    simp only [fill_nil] at hsrc; subst hsrc
    rcases hab with ⟨rfl, _⟩ | ⟨_, rfl⟩ <;> cases Hbase
  | append_singleton K' Ki =>
    cases Ki <;> simp only [fill_append, fill_cons, fill_nil, fillItem, ECtxItem.fill, Exp.cmpXchg.injEq, reduceCtorEq] at hsrc
    all_goals rcases hab with ⟨rfl, v, rfl⟩ | ⟨⟨v, rfl⟩, rfl⟩
    all_goals first
      | exact baseStep_fill_eq_val_absurd Hbase hsrc.1
      | exact baseStep_fill_eq_val_absurd Hbase hsrc.2.1
      | exact baseStep_fill_eq_val_absurd Hbase hsrc.2.2
      | exact fill_var_absurd Hbase hsrc.2.1
      | exact fill_var_absurd Hbase hsrc.2.2
      | exact fill_var_absurd Hbase hsrc.1
end W6c2

namespace W6c2
open Iris Iris.BI Iris.HeapLang Iris.Std Iris.ProgramLogic Language.Notation FromMathlib
open Iris.ProgramLogic.EctxLanguage Iris.ProgramLogic.EctxItemLanguage
/-- State with heap `h0` and the single used prophecy `p0` (written as `new_proph` produces it). -/
abbrev σP (h0 : HeapF (Option Val)) (p0 : ProphId) : HeapLang.State :=
  { heap := h0, usedProphId := ({p0} ∪ (∅ : Std.ExtTreeSet ProphId compare)) }
/-- `adeqP` with an extra prophecy token `proph p0 pvs` handed to the program. -/
theorem adeqPr (e : Exp) (h0 : HeapF (Option Val)) (p0 : ProphId) (φ : Val → Prop)
    (Hwp : ∀ [HeapLangGS .hasLC HeapLangS] (pvs : List (Val × Val)),
      ⊢ iprop(BI.bigSepM (M := HeapF) (fun l v => pointsTo l (DFrac.own 1) v) h0 -∗ proph p0 pvs -∗ WP e {{ v, ⌜φ v⌝ }})) :
    adequate .NotStuck e (σP h0 p0) (fun v _ => φ v) := by
  refine wp_adequacy (GF := HeapLangS) .NotStuck e _ φ ?_
  intro inst κs
  imod genHeap_init (GF := HeapLangS) (H := HeapF) h0 with ⟨%γh, ⟨Hh, Hpts, _⟩⟩
  imod invHeap_init Loc _ (GF := HeapLangS) (H := HeapF) (E:= ⊤) with ⟨%γi, >Hi⟩
  imod (ProphMap.init κs (∅ : Std.ExtTreeSet ProphId compare)) with ⟨%Gproph, Hproph⟩
  letI instHeapLangGS : HeapLangGS .hasLC HeapLangS := ⟨γh, Gproph, γi⟩
  imod (ProphMap.new_proph p0 (∅ : Std.ExtTreeSet ProphId compare) κs (by simp)) $$ Hproph with ⟨Hproph, Hp⟩
  imodintro
  iexists (fun σ κs => iprop% Iris.genHeapInterp σ.heap ∗ Iris.prophMapInterp κs σ.usedProphId)
  iexists (fun _ => iprop(True))
  simp only []
  ihave Hwp := (@Hwp _ _) $$ Hpts Hp
  iframe Hwp Hproph Hh
theorem stuck_falsePr (e : Exp) (h0 : HeapF (Option Val)) (p0 : ProphId) (hv : toVal e = none)
    (hirr : PrimStep.Irreducible (e, σP h0 p0))
    (Hwp : ∀ [HeapLangGS .hasLC HeapLangS] (pvs : List (Val × Val)),
      ⊢ iprop(BI.bigSepM (M := HeapF) (fun l v => pointsTo l (DFrac.own 1) v) h0 -∗ proph p0 pvs -∗ WP e {{ _r, True }})) :
    False := by
  have had := adeqPr e h0 p0 (fun _ => True) Hwp
  rcases had.adequate_not_stuck [e] _ e rfl (.refl) (List.mem_singleton_self e) with h | ⟨obs, e', σ', efs, hs⟩
  · simp [hv] at h
  · exact hirr _ _ _ _ hs
theorem wrong_valPr (e : Exp) (h0 : HeapF (Option Val)) (p0 : ProphId) (σ' : HeapLang.State) (κ : List Observation) (w v : Val)
    (hstep : PrimStep.primStep (e, σP h0 p0) κ (Exp.val w, σ', [])) (hne : w ≠ v)
    (Hwp : ∀ [HeapLangGS .hasLC HeapLangS] (pvs : List (Val × Val)),
      ⊢ iprop(BI.bigSepM (M := HeapF) (fun l v => pointsTo l (DFrac.own 1) v) h0 -∗ proph p0 pvs -∗ WP e {{ r, ⌜r = v⌝ }})) :
    False :=
  hne ((adeqPr e h0 p0 (fun r => r = v) Hwp).adequate_result [] σ' w (.tail .refl ⟨κ, .of_primStep hstep (t₁ := []) (t₂ := [])⟩))
/-- `resolve e v1 v2` is stuck when `e` has no base step to a value and only values sit in its evaluation positions. -/
theorem res_irr (e : Exp) (σ : HeapLang.State) (v1 v2 : Val)
    (hb : ∀ κ v σ' efs, ¬ BaseStep e σ κ (.val v) σ' efs)
    (hctx : ∀ (Ki : ECtxItem) x, e = Ki.fill x → ∃ u, x = .val u) :
    PrimStep.Irreducible (Exp.resolve e (.val v1) (.val v2), σ) := by
  intro obs e' σ' eₜ hstep
  generalize hsrc : Exp.resolve e (.val v1) (.val v2) = src at hstep
  obtain ⟨Hbase⟩ := hstep
  rename_i e₁' e₂' K
  cases K using List.reverseRec with
  | nil =>
    simp only [fill_nil] at hsrc; subst hsrc
    cases Hbase with | resolveS _ _ _ _ _ _ _ _ hi _ => exact hb _ _ _ _ hi
  | append_singleton K' Ki =>
    cases Ki <;>
      simp only [fill_append, fill_cons, fill_nil, fillItem, ECtxItem.fill,
        Exp.resolve.injEq, reduceCtorEq] at hsrc
    case resolveL =>
      obtain ⟨u, hu⟩ := hctx _ _ hsrc.1
      exact baseStep_fill_eq_val_absurd Hbase hu.symm
    case resolveM => exact baseStep_fill_eq_val_absurd Hbase hsrc.2.1
    case resolveR => exact baseStep_fill_eq_val_absurd Hbase hsrc.2.2
/-- A non-atomic expression: it steps to a non-value. -/
abbrev E2 : Exp := .if (.val (.lit (.bool true))) (.if (.val (.lit (.bool true))) (.val vU) (.val vU)) (.val vU)
theorem E2_irr (σ : HeapLang.State) (v1 v2 : Val) : PrimStep.Irreducible (Exp.resolve E2 (.val v1) (.val v2), σ) :=
  res_irr _ _ _ _ (fun _ _ _ _ hb => by cases hb) (fun Ki x h => by
    cases Ki <;> simp [ECtxItem.fill] at h
    exact ⟨_, h.1.symm⟩)
theorem val_res_irr (u : Val) (σ : HeapLang.State) (v1 v2 : Val) : PrimStep.Irreducible (Exp.resolve (.val u) (.val v1) (.val v2), σ) :=
  res_irr _ _ _ _ (fun _ _ _ _ hb => by cases hb) (fun Ki x h => by cases Ki <;> simp [ECtxItem.fill] at h)
theorem cx_res_irr (L : Loc) (vl v1 v2 pv w : Val) (h0 : HeapF (Option Val)) (p0 : ProphId)
    (hL : (σP h0 p0).get? L = some (some vl)) (hs : vl.compareSafe v1 = false) :
    PrimStep.Irreducible (Exp.resolve (Exp.cmpXchg (.val (.lit (.loc L))) (.val v1) (.val v2)) (.val pv) (.val w), σP h0 p0) :=
  res_irr _ _ _ _ (fun _ _ _ _ hb => by
      cases hb with
      | cmpXchgS _ _ _ vl' _ _ hg hsafe _ => rw [hL] at hg; cases hg; simp_all)
    (fun Ki x h => by
      cases Ki <;> simp [ECtxItem.fill] at h
      all_goals first | exact ⟨_, h.1.symm⟩ | exact ⟨_, h.2.1.symm⟩ | exact ⟨_, h.2.2.symm⟩)
theorem hp_get0 (v : Val) (p0 : ProphId) :
    (σP (PartialMap.singleton (M := HeapF) ⟨0⟩ (some v)) p0).get? (⟨0⟩ : Loc) = some (some v) := by
  simp [State.get?, PartialMap.singleton, LawfulPartialMap.get?_insert]
theorem atomic_val (u : Val) : Language.Atomic (State := HeapLang.State) Language.Atomicity.StronglyAtomic (Exp.val u) :=
  ⟨fun hs => (Language.val_irreducible (State := HeapLang.State) rfl _ _ _ _ _ hs).elim⟩
end W6c2

namespace W6c2
open Iris Iris.BI Iris.HeapLang Iris.Std Iris.ProgramLogic COFE
/-- Every slot is the RwSpinLock ghost functor. -/
def GFr : BundledGFunctors := fun _ => ⟨Iris.HeapLang.RwSpinLock.RwSpinLockF⟩
instance rwG_GFr : Iris.HeapLang.RwSpinLock.RwSpinLockG GFr := { elemG := { τ := 0, transp := rfl } }
theorem bupd_false_unsound {GF : BundledGFunctors} (H : ⊢ (|==> iprop(⌜False⌝) : IProp GF)) : False :=
  pure_soundness (PROP := IProp GF) (UPred.bupd_soundness H)
end W6c2

open Iris Iris.BI Iris.HeapLang Iris.Std Iris.ProgramLogic Language.Notation FromMathlib
open Iris.ProgramLogic.Language Iris.ProgramLogic.EctxLanguage Iris.ProgramLogic.EctxItemLanguage COFE W6c2

-- `Iris.HeapLang.Binder.setInsert_mono` idx 3: necessary (b = anon, X = {a}, Y = empty)
theorem w6c2_1 : ¬ drop0% Iris.HeapLang.Binder.setInsert_mono 3 := fun h => by
  have := @h .anon {"a"} ∅ "a" (by simp [Binder.setInsert])
  simp [Binder.setInsert] at this

-- `Iris.HeapLang.Exp.isClosed_weaken` idx 4: necessary (e = var a, X = {a}, Y = empty)
theorem w6c2_2 : ¬ drop0% Iris.HeapLang.Exp.isClosed_weaken 4 := fun h => by
  have := @h {"a"} ∅ (.var "a") (by decide)
  simp [va_nc] at this

-- `Iris.HeapLang.Exp.substStr_substStr_ne` idx 5: necessary (x = y = a, e = var a, v = #0, v' = #1)
theorem w6c2_3 : ¬ drop0% Iris.HeapLang.Exp.substStr_substStr_ne 5 := fun h => by
  have := @h "a" "a" (.lit (.int 0)) (.lit (.int 1)) (.var "a")
  simp at this <;> cases this

-- `Iris.HeapLang.Exp.isClosed_substStr` idx 4: necessary (v = rec anon anon (var b) not closed, e = var a)
theorem w6c2_4 : ¬ drop0% Iris.HeapLang.Exp.isClosed_substStr 4 := fun h => by
  have := @h ∅ "a" vbad (.var "a") (by decide)
  simp at this <;> exact absurd this (by decide)

-- `Iris.HeapLang.Exp.isClosed_substStr` idx 5: necessary (e = var b, x = a, X = empty)
theorem w6c2_5 : ¬ drop0% Iris.HeapLang.Exp.isClosed_substStr 5 := fun h => by
  have := @h ∅ "a" (.lit .unit) (.var "b") rfl
  simp at this <;> exact absurd this (by decide)

-- `Iris.HeapLang.Exp.substStr_isClosed` idx 4: necessary (e = var a, X = empty, x = a)
theorem w6c2_6 : ¬ drop0% Iris.HeapLang.Exp.substStr_isClosed 4 := fun h => by
  have := @h ∅ "a" (.lit .unit) (.var "a") (by simp)
  simp at this <;> cases this

-- `Iris.HeapLang.Exp.substStr_isClosed` idx 5: necessary (e = var a, X = {a}, x = a)
theorem w6c2_7 : ¬ drop0% Iris.HeapLang.Exp.substStr_isClosed 5 := fun h => by
  have := @h {"a"} "a" (.lit .unit) (.var "a") (by decide)
  simp at this <;> cases this

-- `Iris.HeapLang.Exp.isClosed_subst` idx 4: necessary (b = named a, v not closed, e = var a)
theorem w6c2_8 : ¬ drop0% Iris.HeapLang.Exp.isClosed_subst 4 := fun h => by
  have := @h ∅ (.named "a") vbad (.var "a") (by decide)
  simp [Exp.subst] at this <;> exact absurd this (by decide)

-- `Iris.HeapLang.Exp.isClosed_subst` idx 5: necessary (b = anon, e = var b, X = empty)
theorem w6c2_9 : ¬ drop0% Iris.HeapLang.Exp.isClosed_subst 5 := fun h => by
  have := @h ∅ .anon (.lit .unit) (.var "b") rfl
  simp [Exp.subst] at this <;> exact absurd this (by decide)

-- `Iris.HeapLang.Exp.substStr_isClosed_empty` idx 3: necessary (e = var a, x = a)
theorem w6c2_10 : ¬ drop0% Iris.HeapLang.Exp.substStr_isClosed_empty 3 := fun h => by
  have := @h "a" (.lit .unit) (.var "a")
  simp at this <;> cases this

-- `Iris.HeapLang.Exp.subst_subst_ne` idx 5: necessary (b1 = b2 = named a, e = var a, different values)
theorem w6c2_11 : ¬ drop0% Iris.HeapLang.Exp.subst_subst_ne 5 := fun h => by
  have := @h (.named "a") (.named "a") (.lit (.int 0)) (.lit (.int 1)) (.var "a")
  simp [Exp.subst] at this <;> cases this

-- `Iris.HeapLang.Exp.subst_rec` idx 5: necessary (f = y = anon, b = named a, e = var a)
theorem w6c2_12 : ¬ drop0% Iris.HeapLang.Exp.subst_rec 5 := fun h => by
  have := @h .anon .anon (.named "a") (.lit .unit) (.var "a")
  simp [Exp.subst] at this <;> cases this

-- `Iris.HeapLang.Exp.subst_rec_ne` idx 5: necessary (b = f = named a, y = anon, e = var a)
theorem w6c2_13 : ¬ drop0% Iris.HeapLang.Exp.subst_rec_ne 5 := fun h => by
  have := @h (.named "a") .anon (.named "a") (.lit .unit) (.var "a") (Or.inr rfl)
  simp [Exp.subst] at this <;> cases this

-- `Iris.HeapLang.Exp.subst_rec_ne` idx 6: necessary (b = y = named a, f = anon, e = var a)
theorem w6c2_14 : ¬ drop0% Iris.HeapLang.Exp.subst_rec_ne 6 := fun h => by
  have := @h .anon (.named "a") (.named "a") (.lit .unit) (.var "a") (Or.inr rfl)
  simp [Exp.subst] at this <;> cases this

-- `Iris.HeapLang.BinOp.eval_isClosed` idx 4: necessary (v = rec anon anon (var b) not closed)
theorem w6c2_15 : ¬ drop0% Iris.HeapLang.BinOp.eval_isClosed 4 := fun h => by
  have := @h .plus (.lit .unit) (.lit .unit) vbad
  simp [vbad_nc] at this

-- `Iris.HeapLang.State.isClosed_initHeap` idx 4: necessary (sigma holds a non-closed value at loc 0, n = 0)
theorem w6c2_16 : ¬ drop0% Iris.HeapLang.State.isClosed_initHeap 4 := fun h => by
  have := @h σbad ⟨0⟩ 0 none (by simp)
  have h2 := this ⟨0⟩ vbad (by simp [State.get?, LawfulPartialMap.get?_insert])
  exact absurd h2 (by decide)

-- `Iris.HeapLang.State.isClosed_initHeap` idx 5: necessary (empty sigma, n = 1, ov = some non-closed value)
theorem w6c2_17 : ¬ drop0% Iris.HeapLang.State.isClosed_initHeap 5 := fun h => by
  have := @h default ⟨0⟩ 1 (some vbad) (by intro l v hv; simp [State.get?, default, get?_empty] at hv)
  have h2 := this ⟨0⟩ vbad (by simp [State.get?, LawfulPartialMap.get?_insert])
  exact absurd h2 (by decide)

-- `Iris.HeapLang.BaseStep.isClosed` idx 6: necessary (e1 = #(), e2 = var a, no step)
theorem w6c2_18 : ¬ drop0% Iris.HeapLang.BaseStep.isClosed 6 := fun h => by
  have := @h (.val (.lit .unit)) default [] (.var "a") default [] rfl (by intro l v hv; simp [State.get?, default, get?_empty] at hv)
  exact absurd this.1 (by decide)

-- `Iris.HeapLang.BaseStep.isClosed` idx 7: necessary (recS step from non-closed rec expression)
theorem w6c2_19 : ¬ drop0% Iris.HeapLang.BaseStep.isClosed 7 := fun h => by
  have := @h (.rec_ .anon .anon (.var "b")) default [] (.val vbad) default [] (.recS _ _ _ _) (by intro l v hv; simp [State.get?, default, get?_empty] at hv)
  exact absurd this.1 (by decide)

-- `Iris.HeapLang.BaseStep.isClosed` idx 8: necessary (loadS from a heap holding a non-closed value)
theorem w6c2_20 : ¬ drop0% Iris.HeapLang.BaseStep.isClosed 8 := fun h => by
  have := @h (.load (.val (.lit (.loc ⟨0⟩)))) σbad [] (.val vbad) σbad [] (.loadS _ _ _ (by simp [State.get?, LawfulPartialMap.get?_insert])) rfl
  exact absurd this.1 (by decide)

-- `Iris.HeapLang.Binder.deleteMap_insert_of_ne` idx 7: necessary (b = named x on ExtTreeMap: lookup of x differs (none vs some))
theorem w6c2_21 : ¬ drop0% Iris.HeapLang.Binder.deleteMap_insert_of_ne 7 := fun h => by
  have := congrArg (fun m => PartialMap.get? m "a") (@h VarMapF Unit _ (.named "a") ∅ "a" ())
  simp [Binder.deleteMap, LawfulPartialMap.get?_insert, LawfulPartialMap.get?_delete] at this

-- `Iris.HeapLang.Exp.substMap_of_get?_eq_none` idx 4: necessary (vs = {a := #()}, e = var a)
theorem w6c2_22 : ¬ drop0% Iris.HeapLang.Exp.substMap_of_get?_eq_none 4 := fun h => by
  have := @h VarMapF _ sgA (.var "a")
  simp [Exp.substMap, sgA, LawfulPartialMap.get?_insert] at this

-- `Iris.HeapLang.Exp.substMap_isClosed` idx 5: necessary (X = empty, vs = {a := #()}, e = var a)
theorem w6c2_23 : ¬ drop0% Iris.HeapLang.Exp.substMap_isClosed 5 := fun h => by
  have := @h VarMapF _ ∅ sgA (.var "a") (by simp)
  simp [Exp.substMap, sgA, LawfulPartialMap.get?_insert] at this

-- `Iris.HeapLang.Exp.substMap_isClosed` idx 6: necessary (X = {a}, vs = {a := #()}, e = var a)
theorem w6c2_24 : ¬ drop0% Iris.HeapLang.Exp.substMap_isClosed 6 := fun h => by
  have := @h VarMapF _ {"a"} sgA (.var "a") (by decide)
  simp [Exp.substMap, sgA, LawfulPartialMap.get?_insert] at this

-- `Iris.HeapLang.Exp.substMap_isClosed_empty` idx 4: necessary (vs = {a := #()}, e = var a)
theorem w6c2_25 : ¬ drop0% Iris.HeapLang.Exp.substMap_isClosed_empty 4 := fun h => by
  have := @h VarMapF _ sgA (.var "a")
  simp [Exp.substMap, sgA, LawfulPartialMap.get?_insert] at this

-- `Iris.HeapLang.Exp.isClosed_weaken` idx 3: necessary (e = var a, X = Y = empty)
theorem w6c2_26 : ¬ drop0% Iris.HeapLang.Exp.isClosed_weaken 3 := fun h => by
  have := @h ∅ ∅ (.var "a") (fun _ x => x)
  simp [va_nc] at this

-- `Iris.HeapLang.Exp.isClosed_weaken_empty` idx 2: necessary (e = var a, X = empty)
theorem w6c2_27 : ¬ drop0% Iris.HeapLang.Exp.isClosed_weaken_empty 2 := fun h => by
  have := @h ∅ (.var "a")
  simp [va_nc] at this

-- `Iris.HeapLang.UnOp.eval_isClosed` idx 3: necessary (v' = rec anon anon (var b) not closed)
theorem w6c2_28 : ¬ drop0% Iris.HeapLang.UnOp.eval_isClosed 3 := fun h => by
  have := @h .neg (.lit .unit) vbad
  simp [vbad_nc] at this

-- `Iris.HeapLang.fill_isSome_empty` idx 2: necessary (K = [fst], e = var a)
theorem w6c2_29 : ¬ drop0% Iris.HeapLang.fill_isSome_empty 2 := fun h => by
  have := @h [.fst] (.var "a"); cases this

-- `Iris.HeapLang.toVal_fill_some` idx 3: necessary (K = [], e = var a, v = #())
theorem w6c2_30 : ¬ drop0% Iris.HeapLang.toVal_fill_some 3 := fun h => by
  have := (@h [] (.var "a") vU).2; cases this

-- `Iris.HeapLang.mk_pure_prim_step` idx 2: necessary (e1 = e2 = var a: no base step, hpure vacuous, subredexes are values, but var a is not reducible)
theorem w6c2_31 : ¬ drop0% Iris.HeapLang.mk_pure_prim_step 2 := fun h => by
  have hs : SubredexesAreValues (Exp.var "a") := subredexes_are_values fun Ki e' heq => by
    cases Ki <;> simp [fillItem, ECtxItem.fill] at heq
  have := (@h (.var "a") (.var "a") (fun hb => by cases hb) hs).safe default
  obtain ⟨e', σ', et, hp⟩ := this
  have hb := baseStep_of_primStep hp hs
  cases hb

-- `Iris.HeapLang.mk_pure_prim_step` idx 4: removable (removable: SubredexesAreValues e1 follows from hstep default via base_ctx_step_val and subredexes_are_values)
theorem w6c2_32 : drop% Iris.HeapLang.mk_pure_prim_step 4 := fun hstep hpure =>
  mk_pure_prim_step hstep hpure (subredexes_are_values fun Ki e' heq => base_ctx_step_val (heq ▸ hstep default))

-- `Iris.HeapLang.primStep_val_baseStep` idx 6: necessary (e = var a: no base step to a value)
theorem w6c2_33 : ¬ drop0% Iris.HeapLang.primStep_val_baseStep 6 := fun h => by
  have := @h (.var "a") default [] vU default []; cases this

-- `Iris.HeapLang.base_step_to_val_always_to_val` idx 11: necessary (e1 = if true then a else a steps to var a (not a value))
theorem w6c2_34 : ¬ drop0% Iris.HeapLang.base_step_to_val_always_to_val 11 := fun h => by
  have := @h E1 default [] vU default [] default [] (.var "a") default [] (e1_step _); cases this

-- `Iris.HeapLang.base_step_to_val_always_to_val` idx 12: necessary (e1 = (#(), #()) steps to a value, e2b = var a)
theorem w6c2_35 : ¬ drop0% Iris.HeapLang.base_step_to_val_always_to_val 12 := fun h => by
  have := @h (.pair (.val vU) (.val vU)) default [] (.pair vU vU) default [] default [] (.var "a") default [] (.pairS _ _ _); cases this

-- `Iris.HeapLang.prim_step_to_val_always_to_val` idx 11: necessary (e1 = if true then a else a steps to var a (not a value))
theorem w6c2_36 : ¬ drop0% Iris.HeapLang.prim_step_to_val_always_to_val 11 := fun h => by
  have := @h E1 default [] vU default [] default [] (.var "a") default [] (primStep_of_baseStep (e1_step _)); cases this

-- `Iris.HeapLang.prim_step_to_val_always_to_val` idx 12: necessary (e1 = (#(), #()) steps to a value, e2b = var a)
theorem w6c2_37 : ¬ drop0% Iris.HeapLang.prim_step_to_val_always_to_val 12 := fun h => by
  have := @h (.pair (.val vU) (.val vU)) default [] (.pair vU vU) default [] default [] (.var "a") default [] (primStep_of_baseStep (.pairS _ _ _)); cases this

-- `Iris.HeapLang.base_step_to_val_atomic` idx 7: necessary (e1 = if true then a else a steps to var a: not strongly atomic)
theorem w6c2_38 : ¬ drop0% Iris.HeapLang.base_step_to_val_atomic 7 := fun h => by
  have := (@h E1 default [] vU default [] .StronglyAtomic).atomic (primStep_of_baseStep (e1_step default)); cases this

-- `Iris.HeapLang.base_step_more_proph_ids` idx 6: necessary (sigma with proph 0 used, sigma' = default)
theorem w6c2_39 : ¬ drop0% Iris.HeapLang.base_step_more_proph_ids 6 := fun h => by
  have := @h E1 σp [] E1 default [] ⟨0⟩ (by simp)
  simp [default] at this

-- `Iris.HeapLang.prim_step_more_proph_ids` idx 6: necessary (sigma with proph 0 used, sigma' = default)
theorem w6c2_40 : ¬ drop0% Iris.HeapLang.prim_step_more_proph_ids 6 := fun h => by
  have := @h E1 σp [] E1 default [] ⟨0⟩ (by simp)
  simp [default] at this

-- `Iris.HeapLang.step_resolve` idx 8: necessary (e = fst (if true then a else a): context step inside resolve gives a non-value, no base step)
theorem w6c2_41 : ¬ drop0% Iris.HeapLang.step_resolve 8 := fun h => by
  have := @h (.fst E1) vU vU default default [] _ [] (fill_primStep [ECtxItem.resolveL .fst vU vU] (primStep_of_baseStep (e1_step default)))
  cases this

-- `Iris.HeapLang.step_resolve` idx 9: necessary (e = fst #() (atomic), e2 = var a: resolve base steps only produce values)
theorem w6c2_42 : ¬ drop0% Iris.HeapLang.step_resolve 9 := fun h => by
  have := @h (.fst (.val vU)) vU vU default default [] (.var "a") [] instAtomicFst; cases this

-- `Iris.HeapLang.prim_step_resolve_of_inner` idx 8: necessary (e = #() (irreducible), via irreducible_resolve)
theorem w6c2_43 : ¬ drop0% Iris.HeapLang.prim_step_resolve_of_inner 8 := fun h => by
  have := @h (.val vU) σp default [] vU vU [] ⟨0⟩ (by simp)
  exact irreducible_resolve (val_irreducible rfl σp) _ _ _ _ this

-- `Iris.HeapLang.prim_step_resolve_of_inner` idx 9: necessary (e = fst (#(),#()), empty prophecy set: resolveS needs the prophecy)
theorem w6c2_44 : ¬ drop0% Iris.HeapLang.prim_step_resolve_of_inner 9 := fun h => by
  have := @h (.fst (.val (.pair vU vU))) default default [] vU vU [] ⟨0⟩ (.fstS _ _ _)
  obtain ⟨κ, hs⟩ : ∃ κ, PrimStep.primStep (Exp.resolve (.fst (.val (.pair vU vU))) (.val (.lit (.prophecy ⟨0⟩))) (.val vU), (default : HeapLang.State)) κ (Exp.val vU, default, []) := ⟨_, this⟩
  cases step_resolve (hatom := instAtomicFst) hs; simp_all [default]

-- `Iris.HeapLang.step_resolve_decompose` idx 8: necessary (e = fst (if true then a else a): context step, e2 not a value)
theorem w6c2_45 : ¬ drop0% Iris.HeapLang.step_resolve_decompose 8 := fun h => by
  have := @h (.fst E1) ⟨0⟩ vU default default [] _ [] (fill_primStep [ECtxItem.resolveL .fst (.lit (.prophecy ⟨0⟩)) vU] (primStep_of_baseStep (e1_step default)))
  obtain ⟨_, _, _, h2, _⟩ := this; cases h2

-- `Iris.HeapLang.step_resolve_decompose` idx 9: necessary (e = fst #() (atomic), e2 = var a)
theorem w6c2_46 : ¬ drop0% Iris.HeapLang.step_resolve_decompose 9 := fun h => by
  have := @h (.fst (.val vU)) ⟨0⟩ vU default default [] (.var "a") [] instAtomicFst
  obtain ⟨_, _, _, h2, _⟩ := this; cases h2

-- `Iris.HeapLang.resolve_reducible` idx 4: necessary (e = if true then a else a: base reducible only to var a, so resolveS impossible)
theorem w6c2_47 : ¬ drop0% Iris.HeapLang.resolve_reducible 4 := fun h => by
  have := @h E1 σp ⟨0⟩ vU ⟨[], _, _, _, e1_step σp⟩ (by simp)
  obtain ⟨κ, e', σ', efs, hs⟩ := this
  cases hs with | resolveS _ _ _ _ _ _ _ _ hi _ => cases hi

-- `Iris.HeapLang.resolve_reducible` idx 5: necessary (e = fst #() (atomic, stuck))
theorem w6c2_48 : ¬ drop0% Iris.HeapLang.resolve_reducible 5 := fun h => by
  have := @h (.fst (.val vU)) σp ⟨0⟩ vU instAtomicFst (by simp)
  obtain ⟨κ, e', σ', efs, hs⟩ := this
  cases hs with | resolveS _ _ _ _ _ _ _ _ hi _ => cases hi

-- `Iris.HeapLang.resolve_reducible` idx 6: necessary (e = fst (#(),#()), empty prophecy set)
theorem w6c2_49 : ¬ drop0% Iris.HeapLang.resolve_reducible 6 := fun h => by
  have := @h (.fst (.val (.pair vU vU))) default ⟨0⟩ vU instAtomicFst ⟨[], _, _, _, .fstS _ _ _⟩
  obtain ⟨κ, e', σ', efs, hs⟩ := this
  cases hs; simp_all [default]

-- `Iris.HeapLang.prim_step_reducible_resolve` idx 5: necessary (e = fst (#(),#()), empty prophecy set, step_resolve)
theorem w6c2_50 : ¬ drop0% Iris.HeapLang.prim_step_reducible_resolve 5 := fun h => by
  have := @h (.fst (.val (.pair vU vU))) default ⟨0⟩ vU instAtomicFst ⟨[], _, _, _, primStep_of_baseStep (.fstS _ _ _)⟩
  obtain ⟨κ, e', σ', efs, hs⟩ := this
  cases step_resolve (hatom := instAtomicFst) hs; simp_all [default]

-- `Iris.HeapLang.prim_step_reducible_resolve` idx 6: necessary (e = fst #() (atomic, stuck))
theorem w6c2_51 : ¬ drop0% Iris.HeapLang.prim_step_reducible_resolve 6 := fun h => by
  have := @h (.fst (.val vU)) σp ⟨0⟩ vU instAtomicFst (by simp)
  obtain ⟨κ, e', σ', efs, hs⟩ := this
  cases step_resolve (hatom := instAtomicFst) hs with | resolveS _ _ _ _ _ _ _ _ hi _ => cases hi

-- `Iris.HeapLang.irreducible_resolve` idx 4: necessary (e = fst (#(),#()), v1 = prophecy 0 in use: resolveS step)
theorem w6c2_52 : ¬ drop0% Iris.HeapLang.irreducible_resolve 4 := fun h =>
  @h (.fst (.val (.pair vU vU))) (.lit (.prophecy ⟨0⟩)) vU σp _ _ _ _
    (primStep_of_baseStep (.resolveS ⟨0⟩ _ _ σp _ σp [] [] (.fstS _ _ _) (by simp)))

-- `Iris.HeapLang.instAtomicResolve` idx 4: necessary (e = fst (if true ...): resolve steps via context to a non-value)
theorem w6c2_53 : ¬ drop0% Iris.HeapLang.instAtomicResolve 4 := fun h => by
  have := (@h .StronglyAtomic (.fst E1) vU vU).atomic (fill_primStep [ECtxItem.resolveL .fst vU vU] (primStep_of_baseStep (e1_step default)))
  cases this

-- `Iris.HeapLang.prim_step_reducible_resolve` idx 4: necessary (e = if true then a else a: reducible, but resolve e .. is irreducible (no resolveL context into an if-condition value, resolveS needs a value result))
theorem w6c2_54 : ¬ drop0% Iris.HeapLang.prim_step_reducible_resolve 4 := fun h => by
  have := @h E1 σp ⟨0⟩ vU (by simp [σp]) ⟨[], _, _, _, primStep_of_baseStep (e1_step σp)⟩
  obtain ⟨κ, e', σ', efs, hs⟩ := this
  exact res_E1_irred σp _ _ _ _ _ _ hs

-- `Iris.HeapLang.mk_pure_prim_step` idx 3: removable (removable: every HeapLang base step that exists in all states without changing them is deterministic (case analysis on both steps; impure rules contradict hstep at the empty state))
theorem w6c2_55 : drop% Iris.HeapLang.mk_pure_prim_step 3 := fun {e1 e2} hstep hsub => by
  refine mk_pure_prim_step hstep (fun {σ1 κs e2' σ2 efs} hb => ?_) hsub
  obtain ⟨σ', κ0, ef0, hσ, hκ, hef, h0⟩ : ∃ σ' κ0 ef0, σ' = (default : HeapLang.State) ∧ κ0 = [] ∧ ef0 = [] ∧ BaseStep e1 default κ0 e2 σ' ef0 :=
    ⟨_, _, _, rfl, rfl, rfl, hstep default⟩
  cases hb <;> cases h0 <;> simp_all
  all_goals exfalso
  all_goals first
    | (simp_all [State.get?, default, get?_empty]; done)
    | exact alloc_ne _ _ _ (by assumption) hσ
    | exact proph_ne _ hσ

-- `Iris.HeapLang.twp_allocN` idx 7: necessary (n = 0: allocN(#0, #()) is stuck in the empty heap; adequacy (custom adeqP over HeapLangS) gives a contradiction)
theorem w6c2_56 : ¬ drop0% Iris.HeapLang.twp_allocN 7 := fun h => by
  refine stuck_false hl(allocn(#(0:Int), &vU)) (default) rfl
    (irr_of_base (subredexes_are_values fun Ki e' heq => by cases Ki <;> cases heq <;> rfl)
      (fun _ _ _ _ hb => by cases hb <;> first | omega | simp_all [State.get?, default, get?_empty] | (simp_all [State.get?, PartialMap.singleton, LawfulPartialMap.get?_insert, loc_add_zero, get?_empty, Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]; done))) ?_
  intro inst; iintro -
  iapply Iris.twp.to_wp
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (v := vU) (n := 0))
  · itrivial
  · iintro %l -; itrivial

-- `Iris.HeapLang.wp_allocN` idx 7: necessary (n = 0: allocN(#0, #()) is stuck in the empty heap; adequacy (custom adeqP over HeapLangS) gives a contradiction)
theorem w6c2_57 : ¬ drop0% Iris.HeapLang.wp_allocN 7 := fun h => by
  refine stuck_false hl(allocn(#(0:Int), &vU)) (default) rfl
    (irr_of_base (subredexes_are_values fun Ki e' heq => by cases Ki <;> cases heq <;> rfl)
      (fun _ _ _ _ hb => by cases hb <;> first | omega | simp_all [State.get?, default, get?_empty] | (simp_all [State.get?, PartialMap.singleton, LawfulPartialMap.get?_insert, loc_add_zero, get?_empty, Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]; done))) ?_
  intro inst; iintro -
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (v := vU) (n := 0))
  · itrivial
  · inext; iintro %l -; itrivial

-- `Iris.HeapLang.twp_allocN_vec` idx 7: necessary (n = 0: allocN(#0, #()) is stuck in the empty heap; adequacy (custom adeqP over HeapLangS) gives a contradiction)
theorem w6c2_58 : ¬ drop0% Iris.HeapLang.twp_allocN_vec 7 := fun h => by
  refine stuck_false hl(allocn(#(0:Int), &vU)) (default) rfl
    (irr_of_base (subredexes_are_values fun Ki e' heq => by cases Ki <;> cases heq <;> rfl)
      (fun _ _ _ _ hb => by cases hb <;> first | omega | simp_all [State.get?, default, get?_empty] | (simp_all [State.get?, PartialMap.singleton, LawfulPartialMap.get?_insert, loc_add_zero, get?_empty, Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]; done))) ?_
  intro inst; iintro -
  iapply Iris.twp.to_wp
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (v := vU) (n := 0))
  · itrivial
  · iintro %l -; itrivial

-- `Iris.HeapLang.wp_allocN_vec` idx 7: necessary (n = 0: allocN(#0, #()) is stuck in the empty heap; adequacy (custom adeqP over HeapLangS) gives a contradiction)
theorem w6c2_59 : ¬ drop0% Iris.HeapLang.wp_allocN_vec 7 := fun h => by
  refine stuck_false hl(allocn(#(0:Int), &vU)) (default) rfl
    (irr_of_base (subredexes_are_values fun Ki e' heq => by cases Ki <;> cases heq <;> rfl)
      (fun _ _ _ _ hb => by cases hb <;> first | omega | simp_all [State.get?, default, get?_empty] | (simp_all [State.get?, PartialMap.singleton, LawfulPartialMap.get?_insert, loc_add_zero, get?_empty, Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]; done))) ?_
  intro inst; iintro -
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (v := vU) (n := 0))
  · itrivial
  · inext; iintro %l -; itrivial

-- `Iris.HeapLang.twp_allocN_seq` idx 7: necessary (n = 0: allocN(#0, #()) is stuck in the empty heap; adequacy (custom adeqP over HeapLangS) gives a contradiction)
theorem w6c2_60 : ¬ drop0% Iris.HeapLang.twp_allocN_seq 7 := fun h => by
  refine stuck_false hl(allocn(#(0:Int), &vU)) (default) rfl
    (irr_of_base (subredexes_are_values fun Ki e' heq => by cases Ki <;> cases heq <;> rfl)
      (fun _ _ _ _ hb => by cases hb <;> first | omega | simp_all [State.get?, default, get?_empty] | (simp_all [State.get?, PartialMap.singleton, LawfulPartialMap.get?_insert, loc_add_zero, get?_empty, Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]; done))) ?_
  intro inst; iintro -
  iapply Iris.twp.to_wp
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (v := vU) (n := 0))
  · itrivial
  · iintro %l -; itrivial

-- `Iris.HeapLang.wp_allocN_seq` idx 7: necessary (n = 0: allocN(#0, #()) is stuck in the empty heap; adequacy (custom adeqP over HeapLangS) gives a contradiction)
theorem w6c2_61 : ¬ drop0% Iris.HeapLang.wp_allocN_seq 7 := fun h => by
  refine stuck_false hl(allocn(#(0:Int), &vU)) (default) rfl
    (irr_of_base (subredexes_are_values fun Ki e' heq => by cases Ki <;> cases heq <;> rfl)
      (fun _ _ _ _ hb => by cases hb <;> first | omega | simp_all [State.get?, default, get?_empty] | (simp_all [State.get?, PartialMap.singleton, LawfulPartialMap.get?_insert, loc_add_zero, get?_empty, Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]; done))) ?_
  intro inst; iintro -
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (v := vU) (n := 0))
  · itrivial
  · inext; iintro %l -; itrivial

-- `Iris.HeapLang.twp_load_offset` idx 10: necessary (vs = []: the load from an unallocated location is stuck; adequacy)
theorem w6c2_62 : ¬ drop0% Iris.HeapLang.twp_load_offset 10 := fun h => by
  refine stuck_false hl(!v(#((⟨0⟩:Loc) + (0:Nat)))) (default) rfl
    (irr_of_base (subredexes_are_values fun Ki e' heq => by cases Ki <;> cases heq <;> rfl)
      (fun _ _ _ _ hb => by cases hb <;> first | omega | simp_all [State.get?, default, get?_empty] | (simp_all [State.get?, PartialMap.singleton, LawfulPartialMap.get?_insert, loc_add_zero, get?_empty, Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]; done))) ?_
  intro inst; iintro -
  iapply Iris.twp.to_wp
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (dq := .own 1) (v := vU) (vs := []) (off := 0))
  · iapply array_nil.2; itrivial
  · iintro -; itrivial

-- `Iris.HeapLang.wp_load_offset` idx 10: necessary (vs = []: the load from an unallocated location is stuck; adequacy)
theorem w6c2_63 : ¬ drop0% Iris.HeapLang.wp_load_offset 10 := fun h => by
  refine stuck_false hl(!v(#((⟨0⟩:Loc) + (0:Nat)))) (default) rfl
    (irr_of_base (subredexes_are_values fun Ki e' heq => by cases Ki <;> cases heq <;> rfl)
      (fun _ _ _ _ hb => by cases hb <;> first | omega | simp_all [State.get?, default, get?_empty] | (simp_all [State.get?, PartialMap.singleton, LawfulPartialMap.get?_insert, loc_add_zero, get?_empty, Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]; done))) ?_
  intro inst; iintro -
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (dq := .own 1) (v := vU) (vs := []) (off := 0))
  · inext; iapply array_nil.2; itrivial
  · inext; iintro -; itrivial

-- `Iris.HeapLang.twp_store_offset` idx 10: necessary (vs = []: the store to an unallocated location is stuck; adequacy)
theorem w6c2_64 : ¬ drop0% Iris.HeapLang.twp_store_offset 10 := fun h => by
  refine stuck_false hl(v(#((⟨0⟩:Loc) + (0:Nat))) ← &vU) (default) rfl
    (irr_of_base (subredexes_are_values fun Ki e' heq => by cases Ki <;> cases heq <;> rfl)
      (fun _ _ _ _ hb => by cases hb <;> first | omega | simp_all [State.get?, default, get?_empty] | (simp_all [State.get?, PartialMap.singleton, LawfulPartialMap.get?_insert, loc_add_zero, get?_empty, Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]; done))) ?_
  intro inst; iintro -
  iapply Iris.twp.to_wp
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (v := vU) (vs := []) (off := 0) (w := vU))
  · iapply array_nil.2; itrivial
  · iintro -; itrivial

-- `Iris.HeapLang.wp_store_offset` idx 10: necessary (vs = []: the store to an unallocated location is stuck; adequacy)
theorem w6c2_65 : ¬ drop0% Iris.HeapLang.wp_store_offset 10 := fun h => by
  refine stuck_false hl(v(#((⟨0⟩:Loc) + (0:Nat))) ← &vU) (default) rfl
    (irr_of_base (subredexes_are_values fun Ki e' heq => by cases Ki <;> cases heq <;> rfl)
      (fun _ _ _ _ hb => by cases hb <;> first | omega | simp_all [State.get?, default, get?_empty] | (simp_all [State.get?, PartialMap.singleton, LawfulPartialMap.get?_insert, loc_add_zero, get?_empty, Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]; done))) ?_
  intro inst; iintro -
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (v := vU) (vs := []) (off := 0) (w := vU))
  · inext; iapply array_nil.2; itrivial
  · inext; iintro -; itrivial

-- `Iris.HeapLang.twp_xchg_offset` idx 10: necessary (vs = []: xchg on an unallocated location is stuck; adequacy)
theorem w6c2_66 : ¬ drop0% Iris.HeapLang.twp_xchg_offset 10 := fun h => by
  refine stuck_false hl(xchg(#((⟨0⟩:Loc) + (0:Nat)), &vU)) (default) rfl
    (irr_of_base (subredexes_are_values fun Ki e' heq => by cases Ki <;> cases heq <;> rfl)
      (fun _ _ _ _ hb => by cases hb <;> first | omega | simp_all [State.get?, default, get?_empty] | (simp_all [State.get?, PartialMap.singleton, LawfulPartialMap.get?_insert, loc_add_zero, get?_empty, Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]; done))) ?_
  intro inst; iintro -
  iapply Iris.twp.to_wp
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (v := vU) (vs := []) (off := 0) (w := vU))
  · iapply array_nil.2; itrivial
  · iintro -; itrivial

-- `Iris.HeapLang.wp_xchg_offset` idx 10: necessary (vs = []: xchg on an unallocated location is stuck; adequacy)
theorem w6c2_67 : ¬ drop0% Iris.HeapLang.wp_xchg_offset 10 := fun h => by
  refine stuck_false hl(xchg(#((⟨0⟩:Loc) + (0:Nat)), &vU)) (default) rfl
    (irr_of_base (subredexes_are_values fun Ki e' heq => by cases Ki <;> cases heq <;> rfl)
      (fun _ _ _ _ hb => by cases hb <;> first | omega | simp_all [State.get?, default, get?_empty] | (simp_all [State.get?, PartialMap.singleton, LawfulPartialMap.get?_insert, loc_add_zero, get?_empty, Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]; done))) ?_
  intro inst; iintro -
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (v := vU) (vs := []) (off := 0) (w := vU))
  · inext; iapply array_nil.2; itrivial
  · inext; iintro -; itrivial

-- `Iris.HeapLang.twp_cmpXchg_true_offset` idx 11: necessary (vs = []: cmpXchg on an unallocated location is stuck; adequacy)
theorem w6c2_68 : ¬ drop0% Iris.HeapLang.twp_cmpXchg_true_offset 11 := fun h => by
  refine stuck_false hl(cmpXchg(#((⟨0⟩:Loc) + (0:Nat)), &vU, &vU)) (default) rfl
    (irr_of_base (subredexes_are_values fun Ki e' heq => by cases Ki <;> cases heq <;> rfl)
      (fun _ _ _ _ hb => by cases hb <;> first | omega | simp_all [State.get?, default, get?_empty] | (simp_all [State.get?, PartialMap.singleton, LawfulPartialMap.get?_insert, loc_add_zero, get?_empty, Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]; done))) ?_
  intro inst; iintro -
  iapply Iris.twp.to_wp
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (v := vU) (vs := []) (off := 0) (v1 := vU) (v2 := vU) rfl (by decide))
  · iapply array_nil.2; itrivial
  · iintro -; itrivial

-- `Iris.HeapLang.twp_cmpXchg_true_offset` idx 12: necessary (v = #0, v1 = #1, heap 0 -> #0: cmpXchg fails and returns (#0, false), not (#0, true); adequacy)
theorem w6c2_69 : ¬ drop0% Iris.HeapLang.twp_cmpXchg_true_offset 12 := fun h => by
  refine wrong_val hl(cmpXchg(#((⟨0⟩:Loc) + (0:Nat)), &vO, &vU)) (σ1 vZ) _ _ _ hl_val((&vZ, #true)) (primStep_of_baseStep (.cmpXchgS _ vO vU vZ _ false (σ1_get _) rfl rfl)) (by decide) ?_
  intro inst; iintro HP
  iapply Iris.twp.to_wp
  ihave HP := pts1 _ $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (v := vZ) (vs := [vZ]) (off := 0) (v1 := vO) (v2 := vU) rfl (by decide)) $$ [HP]
  · iapply array_singleton.2; iexact HP
  · iintro -; ipureintro; rfl

-- `Iris.HeapLang.twp_cmpXchg_true_offset` idx 13: necessary (v = v1 = (#(),#()) boxed: cmpXchg is stuck (compareSafe fails); adequacy)
theorem w6c2_70 : ¬ drop0% Iris.HeapLang.twp_cmpXchg_true_offset 13 := fun h => by
  refine stuck_false hl(cmpXchg(#((⟨0⟩:Loc) + (0:Nat)), &vP, &vU)) (σ1 vP) rfl
    (cx_unsafe_irr _ _ _ rfl) ?_
  intro inst; iintro HP
  iapply Iris.twp.to_wp
  ihave HP := pts1 _ $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (v := vP) (vs := [vP]) (off := 0) (v1 := vP) (v2 := vU) rfl rfl) $$ [HP]
  · iapply array_singleton.2; iexact HP
  · iintro -; itrivial

-- `Iris.HeapLang.wp_cmpXchg_true_offset` idx 11: necessary (vs = []: cmpXchg on an unallocated location is stuck; adequacy)
theorem w6c2_71 : ¬ drop0% Iris.HeapLang.wp_cmpXchg_true_offset 11 := fun h => by
  refine stuck_false hl(cmpXchg(#((⟨0⟩:Loc) + (0:Nat)), &vU, &vU)) (default) rfl
    (irr_of_base (subredexes_are_values fun Ki e' heq => by cases Ki <;> cases heq <;> rfl)
      (fun _ _ _ _ hb => by cases hb <;> first | omega | simp_all [State.get?, default, get?_empty] | (simp_all [State.get?, PartialMap.singleton, LawfulPartialMap.get?_insert, loc_add_zero, get?_empty, Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]; done))) ?_
  intro inst; iintro -
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (v := vU) (vs := []) (off := 0) (v1 := vU) (v2 := vU) rfl (by decide))
  · inext; iapply array_nil.2; itrivial
  · inext; iintro -; itrivial

-- `Iris.HeapLang.wp_cmpXchg_true_offset` idx 12: necessary (v = #0, v1 = #1, heap 0 -> #0: cmpXchg fails and returns (#0, false), not (#0, true); adequacy)
theorem w6c2_72 : ¬ drop0% Iris.HeapLang.wp_cmpXchg_true_offset 12 := fun h => by
  refine wrong_val hl(cmpXchg(#((⟨0⟩:Loc) + (0:Nat)), &vO, &vU)) (σ1 vZ) _ _ _ hl_val((&vZ, #true)) (primStep_of_baseStep (.cmpXchgS _ vO vU vZ _ false (σ1_get _) rfl rfl)) (by decide) ?_
  intro inst; iintro HP
  ihave HP := pts1 _ $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (v := vZ) (vs := [vZ]) (off := 0) (v1 := vO) (v2 := vU) rfl (by decide)) $$ [HP]
  · inext; iapply array_singleton.2; iexact HP
  · inext; iintro -; ipureintro; rfl

-- `Iris.HeapLang.wp_cmpXchg_true_offset` idx 13: necessary (v = v1 = (#(),#()) boxed: cmpXchg is stuck (compareSafe fails); adequacy)
theorem w6c2_73 : ¬ drop0% Iris.HeapLang.wp_cmpXchg_true_offset 13 := fun h => by
  refine stuck_false hl(cmpXchg(#((⟨0⟩:Loc) + (0:Nat)), &vP, &vU)) (σ1 vP) rfl
    (cx_unsafe_irr _ _ _ rfl) ?_
  intro inst; iintro HP
  ihave HP := pts1 _ $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (v := vP) (vs := [vP]) (off := 0) (v1 := vP) (v2 := vU) rfl rfl) $$ [HP]
  · inext; iapply array_singleton.2; iexact HP
  · inext; iintro -; itrivial

-- `Iris.HeapLang.twp_cmpXchg_fail_offset` idx 12: necessary (vs = []: cmpXchg on an unallocated location is stuck; adequacy)
theorem w6c2_74 : ¬ drop0% Iris.HeapLang.twp_cmpXchg_fail_offset 12 := fun h => by
  refine stuck_false hl(cmpXchg(#((⟨0⟩:Loc) + (0:Nat)), &vO, &vU)) (default) rfl
    (irr_of_base (subredexes_are_values fun Ki e' heq => by cases Ki <;> cases heq <;> rfl)
      (fun _ _ _ _ hb => by cases hb <;> first | omega | simp_all [State.get?, default, get?_empty] | (simp_all [State.get?, PartialMap.singleton, LawfulPartialMap.get?_insert, loc_add_zero, get?_empty, Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]; done))) ?_
  intro inst; iintro -
  iapply Iris.twp.to_wp
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (dq := .own 1) (v := vZ) (vs := []) (off := 0) (v1 := vO) (v2 := vU) (by decide) (by decide))
  · iapply array_nil.2; itrivial
  · iintro -; itrivial

-- `Iris.HeapLang.twp_cmpXchg_fail_offset` idx 13: necessary (v = v1 = #0, heap 0 -> #0: cmpXchg succeeds and returns (#0, true), not (#0, false); adequacy)
theorem w6c2_75 : ¬ drop0% Iris.HeapLang.twp_cmpXchg_fail_offset 13 := fun h => by
  refine wrong_val hl(cmpXchg(#((⟨0⟩:Loc) + (0:Nat)), &vZ, &vU)) (σ1 vZ) _ _ _ hl_val((&vZ, #false)) (primStep_of_baseStep (.cmpXchgS _ vZ vU vZ _ true (σ1_get _) rfl rfl)) (by decide) ?_
  intro inst; iintro HP
  iapply Iris.twp.to_wp
  ihave HP := pts1 _ $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (dq := .own 1) (v := vZ) (vs := [vZ]) (off := 0) (v1 := vZ) (v2 := vU) rfl (by decide)) $$ [HP]
  · iapply array_singleton.2; iexact HP
  · iintro -; ipureintro; rfl

-- `Iris.HeapLang.twp_cmpXchg_fail_offset` idx 14: necessary (v = (#(),#()), v1 = (#(),#0) boxed: cmpXchg is stuck (compareSafe fails); adequacy)
theorem w6c2_76 : ¬ drop0% Iris.HeapLang.twp_cmpXchg_fail_offset 14 := fun h => by
  refine stuck_false hl(cmpXchg(#((⟨0⟩:Loc) + (0:Nat)), &vQ, &vU)) (σ1 vP) rfl
    (cx_unsafe_irr _ _ _ rfl) ?_
  intro inst; iintro HP
  iapply Iris.twp.to_wp
  ihave HP := pts1 _ $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (dq := .own 1) (v := vP) (vs := [vP]) (off := 0) (v1 := vQ) (v2 := vU) rfl (by decide)) $$ [HP]
  · iapply array_singleton.2; iexact HP
  · iintro -; itrivial

-- `Iris.HeapLang.wp_cmpXchg_fail_offset` idx 12: necessary (vs = []: cmpXchg on an unallocated location is stuck; adequacy)
theorem w6c2_77 : ¬ drop0% Iris.HeapLang.wp_cmpXchg_fail_offset 12 := fun h => by
  refine stuck_false hl(cmpXchg(#((⟨0⟩:Loc) + (0:Nat)), &vO, &vU)) (default) rfl
    (irr_of_base (subredexes_are_values fun Ki e' heq => by cases Ki <;> cases heq <;> rfl)
      (fun _ _ _ _ hb => by cases hb <;> first | omega | simp_all [State.get?, default, get?_empty] | (simp_all [State.get?, PartialMap.singleton, LawfulPartialMap.get?_insert, loc_add_zero, get?_empty, Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]; done))) ?_
  intro inst; iintro -
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (dq := .own 1) (v := vZ) (vs := []) (off := 0) (v1 := vO) (v2 := vU) (by decide) (by decide))
  · inext; iapply array_nil.2; itrivial
  · inext; iintro -; itrivial

-- `Iris.HeapLang.wp_cmpXchg_fail_offset` idx 13: necessary (v = v1 = #0, heap 0 -> #0: cmpXchg succeeds and returns (#0, true), not (#0, false); adequacy)
theorem w6c2_78 : ¬ drop0% Iris.HeapLang.wp_cmpXchg_fail_offset 13 := fun h => by
  refine wrong_val hl(cmpXchg(#((⟨0⟩:Loc) + (0:Nat)), &vZ, &vU)) (σ1 vZ) _ _ _ hl_val((&vZ, #false)) (primStep_of_baseStep (.cmpXchgS _ vZ vU vZ _ true (σ1_get _) rfl rfl)) (by decide) ?_
  intro inst; iintro HP
  ihave HP := pts1 _ $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (dq := .own 1) (v := vZ) (vs := [vZ]) (off := 0) (v1 := vZ) (v2 := vU) rfl (by decide)) $$ [HP]
  · inext; iapply array_singleton.2; iexact HP
  · inext; iintro -; ipureintro; rfl

-- `Iris.HeapLang.wp_cmpXchg_fail_offset` idx 14: necessary (v = (#(),#()), v1 = (#(),#0) boxed: cmpXchg is stuck (compareSafe fails); adequacy)
theorem w6c2_79 : ¬ drop0% Iris.HeapLang.wp_cmpXchg_fail_offset 14 := fun h => by
  refine stuck_false hl(cmpXchg(#((⟨0⟩:Loc) + (0:Nat)), &vQ, &vU)) (σ1 vP) rfl
    (cx_unsafe_irr _ _ _ rfl) ?_
  intro inst; iintro HP
  ihave HP := pts1 _ $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (dq := .own 1) (v := vP) (vs := [vP]) (off := 0) (v1 := vQ) (v2 := vU) rfl (by decide)) $$ [HP]
  · inext; iapply array_singleton.2; iexact HP
  · inext; iintro -; itrivial

-- `Iris.HeapLang.twp_faa_offset` idx 10: necessary (vs = []: faa on an unallocated location is stuck; adequacy)
theorem w6c2_80 : ¬ drop0% Iris.HeapLang.twp_faa_offset 10 := fun h => by
  refine stuck_false hl(faa(#((⟨0⟩:Loc) + (0:Nat)), #(0:Int))) (default) rfl
    (irr_of_base (subredexes_are_values fun Ki e' heq => by cases Ki <;> cases heq <;> rfl)
      (fun _ _ _ _ hb => by cases hb <;> first | omega | simp_all [State.get?, default, get?_empty] | (simp_all [State.get?, PartialMap.singleton, LawfulPartialMap.get?_insert, loc_add_zero, get?_empty, Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]; done))) ?_
  intro inst; iintro -
  iapply Iris.twp.to_wp
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (vs := []) (off := 0) (i1 := 0) (i2 := 0))
  · iapply array_nil.2; itrivial
  · iintro -; itrivial

-- `Iris.HeapLang.wp_faa_offset` idx 10: necessary (vs = []: faa on an unallocated location is stuck; adequacy)
theorem w6c2_81 : ¬ drop0% Iris.HeapLang.wp_faa_offset 10 := fun h => by
  refine stuck_false hl(faa(#((⟨0⟩:Loc) + (0:Nat)), #(0:Int))) (default) rfl
    (irr_of_base (subredexes_are_values fun Ki e' heq => by cases Ki <;> cases heq <;> rfl)
      (fun _ _ _ _ hb => by cases hb <;> first | omega | simp_all [State.get?, default, get?_empty] | (simp_all [State.get?, PartialMap.singleton, LawfulPartialMap.get?_insert, loc_add_zero, get?_empty, Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed]; done))) ?_
  intro inst; iintro -
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (vs := []) (off := 0) (i1 := 0) (i2 := 0))
  · inext; iapply array_nil.2; itrivial
  · inext; iintro -; itrivial

-- `Iris.HeapLang.twp_cmpXchg_true_offset_vec` idx 11: necessary (ws = [#0], v1 = #1: cmpXchg fails and returns (#0, false), not (#0, true); adequacy)
theorem w6c2_82 : ¬ drop0% Iris.HeapLang.twp_cmpXchg_true_offset_vec 11 := fun h => by
  refine wrong_val (Exp.cmpXchg (.val (.lit (.loc ((⟨0⟩:Loc) + ((0 : Fin 1).val : Int))))) (.val vO) (.val vU)) (σ1 vZ) _ _ _ hl_val((&vZ, #true)) (primStep_of_baseStep (.cmpXchgS ((⟨0⟩:Loc) + ((0 : Fin 1).val : Int)) vO vU vZ _ false (σ1_get _) rfl rfl)) (by decide) ?_
  intro inst; iintro HP
  iapply Iris.twp.to_wp
  ihave HP := pts1 _ $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (sz := 1) (off := 0) (ws := #v[vZ]) (v1 := vO) (v2 := vU) (by decide)) $$ [HP]
  · iapply arr1v; iexact HP
  · iintro -; ipureintro; rfl

-- `Iris.HeapLang.twp_cmpXchg_true_offset_vec` idx 12: necessary (ws = [(#(),#())] = [v1] boxed: cmpXchg is stuck (compareSafe fails); adequacy)
theorem w6c2_83 : ¬ drop0% Iris.HeapLang.twp_cmpXchg_true_offset_vec 12 := fun h => by
  refine stuck_false (Exp.cmpXchg (.val (.lit (.loc ((⟨0⟩:Loc) + ((0 : Fin 1).val : Int))))) (.val vP) (.val vU)) (σ1 vP) rfl
    (cx_unsafe_irr' ((⟨0⟩:Loc) + ((0 : Fin 1).val : Int)) _ _ _ (σ1_get _) rfl) ?_
  intro inst; iintro HP
  iapply Iris.twp.to_wp
  ihave HP := pts1 _ $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (sz := 1) (off := 0) (ws := #v[vP]) (v1 := vP) (v2 := vU) rfl) $$ [HP]
  · iapply arr1v; iexact HP
  · iintro -; itrivial

-- `Iris.HeapLang.wp_cmpXchg_true_offset_vec` idx 11: necessary (ws = [#0], v1 = #1: cmpXchg fails and returns (#0, false), not (#0, true); adequacy)
theorem w6c2_84 : ¬ drop0% Iris.HeapLang.wp_cmpXchg_true_offset_vec 11 := fun h => by
  refine wrong_val (Exp.cmpXchg (.val (.lit (.loc ((⟨0⟩:Loc) + ((0 : Fin 1).val : Int))))) (.val vO) (.val vU)) (σ1 vZ) _ _ _ hl_val((&vZ, #true)) (primStep_of_baseStep (.cmpXchgS ((⟨0⟩:Loc) + ((0 : Fin 1).val : Int)) vO vU vZ _ false (σ1_get _) rfl rfl)) (by decide) ?_
  intro inst; iintro HP
  ihave HP := pts1 _ $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (sz := 1) (off := 0) (ws := #v[vZ]) (v1 := vO) (v2 := vU) (by decide)) $$ [HP]
  · inext; iapply arr1v; iexact HP
  · inext; iintro -; ipureintro; rfl

-- `Iris.HeapLang.wp_cmpXchg_true_offset_vec` idx 12: necessary (ws = [(#(),#())] = [v1] boxed: cmpXchg is stuck (compareSafe fails); adequacy)
theorem w6c2_85 : ¬ drop0% Iris.HeapLang.wp_cmpXchg_true_offset_vec 12 := fun h => by
  refine stuck_false (Exp.cmpXchg (.val (.lit (.loc ((⟨0⟩:Loc) + ((0 : Fin 1).val : Int))))) (.val vP) (.val vU)) (σ1 vP) rfl
    (cx_unsafe_irr' ((⟨0⟩:Loc) + ((0 : Fin 1).val : Int)) _ _ _ (σ1_get _) rfl) ?_
  intro inst; iintro HP
  ihave HP := pts1 _ $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (sz := 1) (off := 0) (ws := #v[vP]) (v1 := vP) (v2 := vU) rfl) $$ [HP]
  · inext; iapply arr1v; iexact HP
  · inext; iintro -; itrivial

-- `Iris.HeapLang.twp_cmpXchg_fail_offset_vec` idx 12: necessary (ws = [#0], v1 = #0: cmpXchg succeeds and returns (#0, true), not (#0, false); adequacy)
theorem w6c2_86 : ¬ drop0% Iris.HeapLang.twp_cmpXchg_fail_offset_vec 12 := fun h => by
  refine wrong_val (Exp.cmpXchg (.val (.lit (.loc ((⟨0⟩:Loc) + ((0 : Fin 1).val : Int))))) (.val vZ) (.val vU)) (σ1 vZ) _ _ _ hl_val((&vZ, #false)) (primStep_of_baseStep (.cmpXchgS ((⟨0⟩:Loc) + ((0 : Fin 1).val : Int)) vZ vU vZ _ true (σ1_get _) rfl rfl)) (by decide) ?_
  intro inst; iintro HP
  iapply Iris.twp.to_wp
  ihave HP := pts1 _ $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (dq := .own 1) (sz := 1) (off := 0) (ws := #v[vZ]) (v1 := vZ) (v2 := vU) (by decide)) $$ [HP]
  · iapply arr1v; iexact HP
  · iintro -; ipureintro; rfl

-- `Iris.HeapLang.twp_cmpXchg_fail_offset_vec` idx 13: necessary (ws = [(#(),#())], v1 = (#(),#0) boxed: cmpXchg is stuck (compareSafe fails); adequacy)
theorem w6c2_87 : ¬ drop0% Iris.HeapLang.twp_cmpXchg_fail_offset_vec 13 := fun h => by
  refine stuck_false (Exp.cmpXchg (.val (.lit (.loc ((⟨0⟩:Loc) + ((0 : Fin 1).val : Int))))) (.val vQ) (.val vU)) (σ1 vP) rfl
    (cx_unsafe_irr' ((⟨0⟩:Loc) + ((0 : Fin 1).val : Int)) _ _ _ (σ1_get _) rfl) ?_
  intro inst; iintro HP
  iapply Iris.twp.to_wp
  ihave HP := pts1 _ $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (dq := .own 1) (sz := 1) (off := 0) (ws := #v[vP]) (v1 := vQ) (v2 := vU) (by decide)) $$ [HP]
  · iapply arr1v; iexact HP
  · iintro -; itrivial

-- `Iris.HeapLang.wp_cmpXchg_fail_offset_vec` idx 12: necessary (ws = [#0], v1 = #0: cmpXchg succeeds and returns (#0, true), not (#0, false); adequacy)
theorem w6c2_88 : ¬ drop0% Iris.HeapLang.wp_cmpXchg_fail_offset_vec 12 := fun h => by
  refine wrong_val (Exp.cmpXchg (.val (.lit (.loc ((⟨0⟩:Loc) + ((0 : Fin 1).val : Int))))) (.val vZ) (.val vU)) (σ1 vZ) _ _ _ hl_val((&vZ, #false)) (primStep_of_baseStep (.cmpXchgS ((⟨0⟩:Loc) + ((0 : Fin 1).val : Int)) vZ vU vZ _ true (σ1_get _) rfl rfl)) (by decide) ?_
  intro inst; iintro HP
  ihave HP := pts1 _ $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (dq := .own 1) (sz := 1) (off := 0) (ws := #v[vZ]) (v1 := vZ) (v2 := vU) (by decide)) $$ [HP]
  · inext; iapply arr1v; iexact HP
  · inext; iintro -; ipureintro; rfl

-- `Iris.HeapLang.wp_cmpXchg_fail_offset_vec` idx 13: necessary (ws = [(#(),#())], v1 = (#(),#0) boxed: cmpXchg is stuck (compareSafe fails); adequacy)
theorem w6c2_89 : ¬ drop0% Iris.HeapLang.wp_cmpXchg_fail_offset_vec 13 := fun h => by
  refine stuck_false (Exp.cmpXchg (.val (.lit (.loc ((⟨0⟩:Loc) + ((0 : Fin 1).val : Int))))) (.val vQ) (.val vU)) (σ1 vP) rfl
    (cx_unsafe_irr' ((⟨0⟩:Loc) + ((0 : Fin 1).val : Int)) _ _ _ (σ1_get _) rfl) ?_
  intro inst; iintro HP
  ihave HP := pts1 _ $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (dq := .own 1) (sz := 1) (off := 0) (ws := #v[vP]) (v1 := vQ) (v2 := vU) (by decide)) $$ [HP]
  · inext; iapply arr1v; iexact HP
  · inext; iintro -; itrivial

-- `Iris.HeapLang.twp_faa_offset_vec` idx 11: necessary (ws = [#0], i1 = 1: faa returns the old value #0, not #1; adequacy)
theorem w6c2_90 : ¬ drop0% Iris.HeapLang.twp_faa_offset_vec 11 := fun h => by
  refine wrong_val (Exp.faa (.val (.lit (.loc ((⟨0⟩:Loc) + ((0 : Fin 1).val : Int))))) (.val (.lit (.int 0)))) (σ1 vZ) _ _ _ hl_val(#(1:Int)) (primStep_of_baseStep (.faaS ((⟨0⟩:Loc) + ((0 : Fin 1).val : Int)) 0 0 _ (σ1_get _))) (by decide) ?_
  intro inst; iintro HP
  iapply Iris.twp.to_wp
  ihave HP := pts1 _ $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (sz := 1) (off := 0) (ws := #v[vZ]) (i1 := 1) (i2 := 0)) $$ [HP]
  · iapply arr1v; iexact HP
  · iintro -; ipureintro; rfl

-- `Iris.HeapLang.wp_faa_offset_vec` idx 11: necessary (ws = [#0], i1 = 1: faa returns the old value #0, not #1; adequacy)
theorem w6c2_91 : ¬ drop0% Iris.HeapLang.wp_faa_offset_vec 11 := fun h => by
  refine wrong_val (Exp.faa (.val (.lit (.loc ((⟨0⟩:Loc) + ((0 : Fin 1).val : Int))))) (.val (.lit (.int 0)))) (σ1 vZ) _ _ _ hl_val(#(1:Int)) (primStep_of_baseStep (.faaS ((⟨0⟩:Loc) + ((0 : Fin 1).val : Int)) 0 0 _ (σ1_get _))) (by decide) ?_
  intro inst; iintro HP
  ihave HP := pts1 _ $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (sz := 1) (off := 0) (ws := #v[vZ]) (i1 := 1) (i2 := 0)) $$ [HP]
  · inext; iapply arr1v; iexact HP
  · inext; iintro -; ipureintro; rfl

-- `Iris.HeapLang.twp_cmpXchg_fail` idx 10: necessary (l -> #0, v1 = #0: cmpXchg succeeds and returns (#0, true); adequacy)
theorem w6c2_92 : ¬ drop0% Iris.HeapLang.twp_cmpXchg_fail 10 := fun h => by
  refine wrong_val (Exp.cmpXchg (.val (.lit (.loc (⟨0⟩:Loc)))) (.val vZ) (.val vU)) (σ1 vZ) _ _ _ hl_val((&vZ, #false)) (primStep_of_baseStep (.cmpXchgS (⟨0⟩:Loc) vZ vU vZ _ true (σ1_get0 _) rfl rfl)) (by decide) ?_
  intro inst; iintro HP
  iapply Iris.twp.to_wp
  ihave HP := pts1 _ $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (q := .own 1) (v' := vZ) (v1 := vZ) (v2 := vU) (by decide)) $$ [HP]
  · iexact HP
  · iintro -; ipureintro; rfl

-- `Iris.HeapLang.twp_cmpXchg_fail` idx 11: necessary (l -> (#(),#()), v1 = (#(),#0) boxed: cmpXchg is stuck; adequacy)
theorem w6c2_93 : ¬ drop0% Iris.HeapLang.twp_cmpXchg_fail 11 := fun h => by
  refine stuck_false (Exp.cmpXchg (.val (.lit (.loc (⟨0⟩:Loc)))) (.val vQ) (.val vU)) (σ1 vP) rfl
    (cx_unsafe_irr' (⟨0⟩:Loc) _ _ _ (σ1_get0 _) rfl) ?_
  intro inst; iintro HP
  iapply Iris.twp.to_wp
  ihave HP := pts1 _ $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (q := .own 1) (v' := vP) (v1 := vQ) (v2 := vU) (by decide)) $$ [HP]
  · iexact HP
  · iintro -; itrivial

-- `Iris.HeapLang.twp_cmpXchg_true` idx 9: necessary (l -> #0, v1 = #1: cmpXchg fails and returns (#0, false); adequacy)
theorem w6c2_94 : ¬ drop0% Iris.HeapLang.twp_cmpXchg_true 9 := fun h => by
  refine wrong_val (Exp.cmpXchg (.val (.lit (.loc (⟨0⟩:Loc)))) (.val vO) (.val vU)) (σ1 vZ) _ _ _ hl_val((&vZ, #true)) (primStep_of_baseStep (.cmpXchgS (⟨0⟩:Loc) vO vU vZ _ false (σ1_get0 _) rfl rfl)) (by decide) ?_
  intro inst; iintro HP
  iapply Iris.twp.to_wp
  ihave HP := pts1 _ $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (v' := vZ) (v1 := vO) (v2 := vU) (by decide)) $$ [HP]
  · iexact HP
  · iintro -; ipureintro; rfl

-- `Iris.HeapLang.twp_cmpXchg_true` idx 10: necessary (l -> (#(),#()) = v1 boxed: cmpXchg is stuck; adequacy)
theorem w6c2_95 : ¬ drop0% Iris.HeapLang.twp_cmpXchg_true 10 := fun h => by
  refine stuck_false (Exp.cmpXchg (.val (.lit (.loc (⟨0⟩:Loc)))) (.val vP) (.val vU)) (σ1 vP) rfl
    (cx_unsafe_irr' (⟨0⟩:Loc) _ _ _ (σ1_get0 _) rfl) ?_
  intro inst; iintro HP
  iapply Iris.twp.to_wp
  ihave HP := pts1 _ $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (v' := vP) (v1 := vP) (v2 := vU) rfl) $$ [HP]
  · iexact HP
  · iintro -; itrivial

-- `Iris.HeapLang.wp_cmpXchg_fail` idx 14: necessary (l -> (#(),#()), e1 = (#(),#0) boxed: cmpXchg is stuck; adequacy)
theorem w6c2_96 : ¬ drop0% Iris.HeapLang.wp_cmpXchg_fail 14 := fun h => by
  refine stuck_false (Exp.cmpXchg (.val (.lit (.loc (⟨0⟩:Loc)))) (.val vQ) (.val vU)) (σ1 vP) rfl
    (cx_unsafe_irr' (⟨0⟩:Loc) _ _ _ (σ1_get0 _) rfl) ?_
  intro inst; iintro HP
  ihave HP := pts1 _ $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (q := .own 1) (v' := vP) (e1 := .val vQ) (v1 := vQ) (e2 := .val vU) (v2 := vU) rfl rfl (by decide)) $$ [HP]
  · inext; iexact HP
  · inext; iintro -; itrivial

-- `Iris.HeapLang.wp_cmpXchg_fail` idx 15: necessary (l -> #0, v1 = #0: cmpXchg succeeds and returns (#0, true); adequacy)
theorem w6c2_97 : ¬ drop0% Iris.HeapLang.wp_cmpXchg_fail 15 := fun h => by
  refine wrong_val (Exp.cmpXchg (.val (.lit (.loc (⟨0⟩:Loc)))) (.val vZ) (.val vU)) (σ1 vZ) _ _ _ hl_val((&vZ, #false)) (primStep_of_baseStep (.cmpXchgS (⟨0⟩:Loc) vZ vU vZ _ true (σ1_get0 _) rfl rfl)) (by decide) ?_
  intro inst; iintro HP
  ihave HP := pts1 _ $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (q := .own 1) (v' := vZ) (e1 := .val vZ) (v1 := vZ) (e2 := .val vU) (v2 := vU) rfl rfl (by decide)) $$ [HP]
  · inext; iexact HP
  · inext; iintro -; ipureintro; rfl

-- `Iris.HeapLang.wp_cmpXchg_true` idx 13: necessary (l -> (#(),#()) = v1 boxed: cmpXchg is stuck; adequacy)
theorem w6c2_98 : ¬ drop0% Iris.HeapLang.wp_cmpXchg_true 13 := fun h => by
  refine stuck_false (Exp.cmpXchg (.val (.lit (.loc (⟨0⟩:Loc)))) (.val vP) (.val vU)) (σ1 vP) rfl
    (cx_unsafe_irr' (⟨0⟩:Loc) _ _ _ (σ1_get0 _) rfl) ?_
  intro inst; iintro HP
  ihave HP := pts1 _ $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (v' := vP) (e1 := .val vP) (v1 := vP) (e2 := .val vU) (v2 := vU) rfl rfl (by decide)) $$ [HP]
  · inext; iexact HP
  · inext; iintro -; itrivial

-- `Iris.HeapLang.wp_cmpXchg_true` idx 14: necessary (l -> #0, v1 = #1: cmpXchg fails and returns (#0, false); adequacy)
theorem w6c2_99 : ¬ drop0% Iris.HeapLang.wp_cmpXchg_true 14 := fun h => by
  refine wrong_val (Exp.cmpXchg (.val (.lit (.loc (⟨0⟩:Loc)))) (.val vO) (.val vU)) (σ1 vZ) _ _ _ hl_val((&vZ, #true)) (primStep_of_baseStep (.cmpXchgS (⟨0⟩:Loc) vO vU vZ _ false (σ1_get0 _) rfl rfl)) (by decide) ?_
  intro inst; iintro HP
  ihave HP := pts1 _ $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (v' := vZ) (e1 := .val vO) (v1 := vO) (e2 := .val vU) (v2 := vU) rfl rfl (by decide)) $$ [HP]
  · inext; iexact HP
  · inext; iintro -; ipureintro; rfl

-- `Iris.HeapLang.heap_adequacy` idx 5: necessary (e = var a is stuck at once, so not adequate)
theorem w6c2_100 : ¬ drop0% Iris.HeapLang.heap_adequacy 5 := fun h => by
  have had := @h HeapLangS _ (.var "a") default (fun _ => True)
  rcases had.adequate_not_stuck [.var "a"] default (.var "a") rfl .refl (List.mem_singleton_self _) with hv | ⟨_, _, _, _, hs⟩
  · cases hv
  · exact var_irr _ _ _ _ _ hs

-- `Iris.HeapLang.wp_rec` idx 11: necessary (vf = #() is not a function: #() #() is stuck while the premise WP #() holds; adequacy)
theorem w6c2_101 : ¬ drop0% Iris.HeapLang.wp_rec 11 := fun h => by
  refine stuck_false hl(v(&vU) v(&vU)) default rfl
    (irr_of_base (subredexes_are_values fun Ki e' heq => by cases Ki <;> cases heq <;> rfl) (fun _ _ _ _ hb => by cases hb)) ?_
  intro inst
  have H : iprop(▷ WP (Exp.val vU) @ Stuckness.NotStuck ; ⊤ {{ _r, True }}) ⊢ WP hl(v(&vU) v(&vU)) @ Stuckness.NotStuck ; ⊤ {{ _r, True }} :=
    h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (f := .anon) (x := .anon) (e := .val vU) (vf := vU) (v := vU)
  iintro -
  iapply H
  inext; iapply wp_value'; itrivial

-- `_private.Iris.HeapLang.DerivedLaws.0.Iris.HeapLang.set_getElem?_self` idx 3: necessary (vs = [#0], off = 0, v = #1)
theorem w6c2_102 : ¬ drop0% _private.Iris.HeapLang.DerivedLaws.«0».Iris.HeapLang.set_getElem?_self 3 := fun h =>
  absurd (@h vO [vZ] 0) (by decide)

-- `Iris.HeapLang.update_array` idx 8: necessary (vs = []: emp would give two full points-to of one cell with different values)
theorem w6c2_103 : ¬ drop0% Iris.HeapLang.update_array 8 := fun h => false_of (by
  intro inst
  exact pt_twice_false _ fun v => (array_nil.2.trans (h (GF := HeapLangS) (hlc := .hasLC) (l := ⟨0⟩) (dq := .own 1) (v := v) (vs := []) (off := 0))).trans BI.sep_elim_left)

-- `_private.Iris.HeapLang.DerivedLaws.0.Iris.HeapLang.update_array_read` idx 8: necessary (vs = []: two full points-to of one cell with different values)
theorem w6c2_104 : ¬ drop0% _private.Iris.HeapLang.DerivedLaws.«0».Iris.HeapLang.update_array_read 8 := fun h => false_of (by
  intro inst
  exact pt_twice_false _ fun v => (array_nil.2.trans (h (GF := HeapLangS) (hlc := .hasLC) (l := ⟨0⟩) (dq := .own 1) (v := v) (vs := []) (off := 0))).trans BI.sep_elim_left)

-- `Iris.HeapLang.frameArrayCons` idx 9: necessary (R = Q = emp: emp would frame a full points-to of every value)
theorem w6c2_105 : ¬ drop0% Iris.HeapLang.frameArrayCons 9 := fun h => false_of (by
  intro inst
  exact pt_twice_false _ fun v => (BI.emp_sep.2.trans ((h (GF := HeapLangS) (hlc := .hasLC) (l := ⟨0⟩) (dq := .own 1) (v := v) (vs := []) (R := iprop(emp)) (Q := iprop(emp))).frame.trans array_singleton.1)))

-- `Iris.HeapLang.wp_cmpXchg_fail` idx 12: necessary (e1 = var a (not a value): cmpXchg(#l, a, #()) is stuck; adequacy)
theorem w6c2_106 : ¬ drop0% Iris.HeapLang.wp_cmpXchg_fail 12 := fun h => by
  refine stuck_false (Exp.cmpXchg (.val (.lit (.loc (⟨0⟩:Loc)))) (.var "a") (.val vU)) (σ1 vZ) rfl
    (cx_var_irr _ _ _ _ (.inl ⟨rfl, _, rfl⟩)) ?_
  intro inst; iintro HP
  ihave HP := pts1 _ $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (q := .own 1) (v' := vZ) (e1 := .var "a") (v1 := vO) (e2 := .val vU) (v2 := vU) rfl (by decide) (by decide)) $$ [HP]
  · inext; iexact HP
  · inext; iintro -; itrivial

-- `Iris.HeapLang.wp_cmpXchg_fail` idx 13: necessary (e2 = var a (not a value): cmpXchg(#l, #1, a) is stuck; adequacy)
theorem w6c2_107 : ¬ drop0% Iris.HeapLang.wp_cmpXchg_fail 13 := fun h => by
  refine stuck_false (Exp.cmpXchg (.val (.lit (.loc (⟨0⟩:Loc)))) (.val vO) (.var "a")) (σ1 vZ) rfl
    (cx_var_irr _ _ _ _ (.inr ⟨⟨_, rfl⟩, rfl⟩)) ?_
  intro inst; iintro HP
  ihave HP := pts1 _ $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (q := .own 1) (v' := vZ) (e1 := .val vO) (v1 := vO) (e2 := .var "a") (v2 := vU) rfl (by decide) (by decide)) $$ [HP]
  · inext; iexact HP
  · inext; iintro -; itrivial

-- `Iris.HeapLang.wp_cmpXchg_true` idx 11: necessary (e1 = var a (not a value): cmpXchg(#l, a, #()) is stuck; adequacy)
theorem w6c2_108 : ¬ drop0% Iris.HeapLang.wp_cmpXchg_true 11 := fun h => by
  refine stuck_false (Exp.cmpXchg (.val (.lit (.loc (⟨0⟩:Loc)))) (.var "a") (.val vU)) (σ1 vZ) rfl
    (cx_var_irr _ _ _ _ (.inl ⟨rfl, _, rfl⟩)) ?_
  intro inst; iintro HP
  ihave HP := pts1 _ $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (v' := vZ) (e1 := .var "a") (v1 := vZ) (e2 := .val vU) (v2 := vU) rfl (by decide) (by decide)) $$ [HP]
  · inext; iexact HP
  · inext; iintro -; itrivial

-- `Iris.HeapLang.wp_cmpXchg_true` idx 12: necessary (e2 = var a (not a value): cmpXchg(#l, #0, a) is stuck; adequacy)
theorem w6c2_109 : ¬ drop0% Iris.HeapLang.wp_cmpXchg_true 12 := fun h => by
  refine stuck_false (Exp.cmpXchg (.val (.lit (.loc (⟨0⟩:Loc)))) (.val vZ) (.var "a")) (σ1 vZ) rfl
    (cx_var_irr _ _ _ _ (.inr ⟨⟨_, rfl⟩, rfl⟩)) ?_
  intro inst; iintro HP
  ihave HP := pts1 _ $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (v' := vZ) (e1 := .val vZ) (v1 := vZ) (e2 := .var "a") (v2 := vU) rfl (by decide) (by decide)) $$ [HP]
  · inext; iexact HP
  · inext; iintro -; itrivial

-- `Iris.HeapLang.wp_resolve_strong` idx 10: necessary (e = if #true then (if #true then #() else #()) else #() is not atomic: resolve e is stuck while WP e holds; adequacy with a prophecy)
theorem w6c2_110 : ¬ drop0% Iris.HeapLang.wp_resolve_strong 10 := fun h => by
  refine stuck_falsePr (Exp.resolve E2 (.val (.lit (.prophecy ⟨0⟩))) (.val vU)) ∅ ⟨0⟩ rfl (E2_irr _ _ _) ?_
  intro inst pvs
  iintro - Hp
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (Φ := fun _ => iprop(True)) (e := E2) (p := ⟨0⟩) (w := vU) (pvs := pvs) rfl) $$ Hp
  iintro Hp
  iapply (wp_pure_step_later (Hexec := instPureExecIfTrue) trivial)
  inext; iintro -
  iapply (wp_pure_step_later (Hexec := instPureExecIfTrue) trivial)
  inext; iintro -
  iapply wp_value'
  iexists pvs; iframe Hp; iintro %pvs'' - -; itrivial

-- `Iris.HeapLang.wp_resolve_strong` idx 11: necessary (e = #(): resolve #() is stuck; adequacy with a prophecy)
theorem w6c2_111 : ¬ drop0% Iris.HeapLang.wp_resolve_strong 11 := fun h => by
  refine stuck_falsePr (Exp.resolve (.val vU) (.val (.lit (.prophecy ⟨0⟩))) (.val vU)) ∅ ⟨0⟩ rfl (val_res_irr _ _ _ _) ?_
  intro inst pvs
  iintro - Hp
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (Φ := fun _ => iprop(True)) (e := .val vU) (p := ⟨0⟩) (w := vU) (pvs := pvs) (atomic_val _)) $$ Hp
  iintro Hp
  iapply wp_value'
  iexists pvs; iframe Hp; iintro %pvs'' - -; itrivial

-- `Iris.HeapLang.wp_resolve` idx 10: necessary (e = if #true then (if #true then #() else #()) else #() is not atomic: resolve e is stuck; adequacy with a prophecy)
theorem w6c2_112 : ¬ drop0% Iris.HeapLang.wp_resolve 10 := fun h => by
  refine stuck_falsePr (Exp.resolve E2 (.val (.lit (.prophecy ⟨0⟩))) (.val vU)) ∅ ⟨0⟩ rfl (E2_irr _ _ _) ?_
  intro inst pvs
  iintro - Hp
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (Φ := fun _ => iprop(True)) (e := E2) (p := ⟨0⟩) (w := vU) (pvs := pvs) rfl) $$ Hp
  iapply (wp_pure_step_later (Hexec := instPureExecIfTrue) trivial)
  inext; iintro -
  iapply (wp_pure_step_later (Hexec := instPureExecIfTrue) trivial)
  inext; iintro -
  iapply wp_value'
  iintro %pvs' - -; itrivial

-- `Iris.HeapLang.wp_resolve` idx 11: necessary (e = #(): resolve #() is stuck; adequacy with a prophecy)
theorem w6c2_113 : ¬ drop0% Iris.HeapLang.wp_resolve 11 := fun h => by
  refine stuck_falsePr (Exp.resolve (.val vU) (.val (.lit (.prophecy ⟨0⟩))) (.val vU)) ∅ ⟨0⟩ rfl (val_res_irr _ _ _ _) ?_
  intro inst pvs
  iintro - Hp
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (Φ := fun _ => iprop(True)) (e := .val vU) (p := ⟨0⟩) (w := vU) (pvs := pvs) (atomic_val _)) $$ Hp
  iapply wp_value'
  iintro %pvs' - -; itrivial

-- `Iris.HeapLang.wp_resolve_cmpXchg_true` idx 11: necessary (v1 = (#(),#()) boxed: the inner cmpXchg is stuck; adequacy with a prophecy)
theorem w6c2_114 : ¬ drop0% Iris.HeapLang.wp_resolve_cmpXchg_true 11 := fun h => by
  refine stuck_falsePr (Exp.resolve (Exp.cmpXchg (.val (.lit (.loc ⟨0⟩))) (.val vP) (.val vU)) (.val (.lit (.prophecy ⟨0⟩))) (.val vU))
    (PartialMap.singleton (M := HeapF) ⟨0⟩ (some vP)) ⟨0⟩ rfl (cx_res_irr _ _ _ _ _ _ _ _ (hp_get0 _ _) rfl) ?_
  intro inst pvs
  iintro HP Hp
  ihave HP := BI.BigSepM.bigSepM_singleton.1 $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (p := ⟨0⟩) (pvs := pvs) (v1 := vP) (v2 := vU) (w := vU)) $$ [HP Hp]
  · isplitl [Hp]; iexact Hp; inext; iexact HP
  · inext; iintro -; itrivial

-- `Iris.HeapLang.wp_resolve_cmpXchg_fail` idx 14: necessary (v = (#(),#()), v1 = (#(),#0) boxed: the inner cmpXchg is stuck; adequacy with a prophecy)
theorem w6c2_115 : ¬ drop0% Iris.HeapLang.wp_resolve_cmpXchg_fail 14 := fun h => by
  refine stuck_falsePr (Exp.resolve (Exp.cmpXchg (.val (.lit (.loc ⟨0⟩))) (.val vQ) (.val vU)) (.val (.lit (.prophecy ⟨0⟩))) (.val vU))
    (PartialMap.singleton (M := HeapF) ⟨0⟩ (some vP)) ⟨0⟩ rfl (cx_res_irr _ _ _ _ _ _ _ _ (hp_get0 _ _) rfl) ?_
  intro inst pvs
  iintro HP Hp
  ihave HP := BI.BigSepM.bigSepM_singleton.1 $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (dq := .own 1) (v := vP) (p := ⟨0⟩) (pvs := pvs) (v1 := vQ) (v2 := vU) (w := vU) (by decide)) $$ [HP Hp]
  · isplitl [Hp]; iexact Hp; inext; iexact HP
  · inext; iintro -; itrivial

-- `Iris.HeapLang.wp_resolve_cmpXchg_fail` idx 13: necessary (v = v1 = #0: the cmpXchg succeeds and resolve returns (#0, true), not (#0, false); adequacy with a prophecy)
theorem w6c2_116 : ¬ drop0% Iris.HeapLang.wp_resolve_cmpXchg_fail 13 := fun h => by
  refine wrong_valPr (Exp.resolve (Exp.cmpXchg (.val (.lit (.loc ⟨0⟩))) (.val vZ) (.val vU)) (.val (.lit (.prophecy ⟨0⟩))) (.val vU))
    (PartialMap.singleton (M := HeapF) ⟨0⟩ (some vZ)) ⟨0⟩ _ _ _ hl_val((&vZ, #false))
    (primStep_of_baseStep (.resolveS ⟨0⟩ _ _ _ vU _ [] [] (.cmpXchgS _ vZ vU vZ _ true (hp_get0 _ _) rfl rfl) (by simp)))
    (by decide) ?_
  intro inst pvs
  iintro HP Hp
  ihave HP := BI.BigSepM.bigSepM_singleton.1 $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (dq := .own 1) (v := vZ) (p := ⟨0⟩) (pvs := pvs) (v1 := vZ) (v2 := vU) (w := vU) (by decide)) $$ [HP Hp]
  · isplitl [Hp]; iexact Hp; inext; iexact HP
  · inext; iintro -; ipureintro; rfl

-- `_private.Iris.HeapLang.Lib.RwSpinLock.0.Iris.HeapLang.RwSpinLock.own_auth_auth_False` idx 7: necessary (q1 = 1/4, q2 = 3/4: the two halves of an allocated full authority; bupd soundness)
theorem w6c2_117 : ¬ drop0% _private.Iris.HeapLang.Lib.RwSpinLock.«0».Iris.HeapLang.RwSpinLock.own_auth_auth_False 7 := fun h => by
  apply bupd_false_unsound (GF := GFr)
  refine (iOwn_alloc (F := RwSpinLock.RwSpinLockF) (● LeibnizMultiSet.ofSet (∅ : RwSpinLock.ReaderFracs)) (Auth.auth_valid.mpr trivial)).trans (BIUpdate.mono ?_)
  refine BI.exists_elim fun γ => ?_
  have e : (● LeibnizMultiSet.ofSet (∅ : RwSpinLock.ReaderFracs) : Auth (LeibnizMultiSet RwSpinLock.ReaderFracs)) =
      Iris.Op.op (●{.own Qp.quarter} LeibnizMultiSet.ofSet (∅ : RwSpinLock.ReaderFracs) : Auth (LeibnizMultiSet RwSpinLock.ReaderFracs))
        (●{.own Qp.threeQuarters} LeibnizMultiSet.ofSet (∅ : RwSpinLock.ReaderFracs)) := by
    rw [← Auth.auth_dfrac_op, DFrac.op_own, Qp.quarter_add_threeQuarters]
  rw [e]
  exact iOwn_op.1.trans (h (GF := GFr) (γ := γ) (q₁ := Qp.quarter) (q₂ := Qp.threeQuarters) (g₁ := ∅) (g₂ := ∅))

-- `Iris.HeapLang.RwSpinLock.auth_valid_singleton` idx 3: necessary (g = empty)
theorem w6c2_118 : ¬ drop0% Iris.HeapLang.RwSpinLock.auth_valid_singleton 3 := fun h => by
  have := @h (.own 1) 1 ∅
  simp at this

-- `Iris.HeapLang.heapArray_toSeq_metaToken` idx 6: necessary (vs = [], n = 1: emp would give two copies of metaToken l top; adequacy)
theorem w6c2_119 : ¬ drop0% Iris.HeapLang.heapArray_toSeq_metaToken 6 := fun h => false_of (by
  intro inst
  have A : ⊢ metaToken ((⟨0⟩:Loc) + ((0:Nat):Int)) (⊤ : CoPset) :=
    (BI.BigSepM.bigSepM_empty.2.trans (h (GF := HeapLangS) (hlc := .hasLC) (l := ⟨0⟩) (vs := []) (n := 1))).trans
      BI.BigSepL.bigSepL_singleton.1
  ihave H1 := A
  ihave H2 := A
  ihave %Hd := metaToken_valid_2 $$ H1 H2
  exact absurd Hd (fun hd => hd .xH ⟨rfl, rfl⟩))
