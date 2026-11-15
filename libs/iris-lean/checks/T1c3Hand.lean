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
namespace T1c3
open Iris Iris.HeapLang Iris.Std Iris.ProgramLogic Language.Notation FromMathlib
open Iris.ProgramLogic.EctxLanguage Iris.ProgramLogic.EctxItemLanguage

def isV : Exp → Bool | .val _ => true | _ => false

/-- Next redex in HeapLang evaluation order (right to left), with its context (innermost first). -/
def dc : Exp → List ECtxItem × Exp
  | .app e1 (.val v2) => if isV e1 then ([], .app e1 (.val v2)) else let p := dc e1; (p.1 ++ [.appL v2], p.2)
  | .app e1 e2 => let p := dc e2; (p.1 ++ [.appR e1], p.2)
  | .unop op (.val v) => ([], .unop op (.val v))
  | .unop op e => let p := dc e; (p.1 ++ [.unOp op], p.2)
  | .binop op e1 (.val v2) => if isV e1 then ([], .binop op e1 (.val v2)) else let p := dc e1; (p.1 ++ [.binOpL op v2], p.2)
  | .binop op e1 e2 => let p := dc e2; (p.1 ++ [.binOpR op e1], p.2)
  | .if (.val v) e1 e2 => ([], .if (.val v) e1 e2)
  | .if e0 e1 e2 => let p := dc e0; (p.1 ++ [.if e1 e2], p.2)
  | .pair e1 (.val v2) => if isV e1 then ([], .pair e1 (.val v2)) else let p := dc e1; (p.1 ++ [.pairL v2], p.2)
  | .pair e1 e2 => let p := dc e2; (p.1 ++ [.pairR e1], p.2)
  | .allocN e1 (.val v2) => if isV e1 then ([], .allocN e1 (.val v2)) else let p := dc e1; (p.1 ++ [.allocNL v2], p.2)
  | .allocN e1 e2 => let p := dc e2; (p.1 ++ [.allocNR e1], p.2)
  | .free (.val v) => ([], .free (.val v))
  | .free e => let p := dc e; (p.1 ++ [.free], p.2)
  | .load (.val v) => ([], .load (.val v))
  | .load e => let p := dc e; (p.1 ++ [.load], p.2)
  | .store e1 (.val v2) => if isV e1 then ([], .store e1 (.val v2)) else let p := dc e1; (p.1 ++ [.storeL v2], p.2)
  | .store e1 e2 => let p := dc e2; (p.1 ++ [.storeR e1], p.2)
  | .fst (.val v) => ([], .fst (.val v))
  | .fst e => let p := dc e; (p.1 ++ [.fst], p.2)
  | .snd (.val v) => ([], .snd (.val v))
  | .snd e => let p := dc e; (p.1 ++ [.snd], p.2)
  | .cmpXchg e0 e1 (.val v2) => match e1 with
    | .val v1 => if isV e0 then ([], .cmpXchg e0 (.val v1) (.val v2)) else let p := dc e0; (p.1 ++ [.cmpXchgL v1 v2], p.2)
    | _ => let p := dc e1; (p.1 ++ [.cmpXchgM e0 v2], p.2)
  | .cmpXchg e0 e1 e2 => let p := dc e2; (p.1 ++ [.cmpXchgR e0 e1], p.2)
  | e => ([], e)

/-- Head step: pure redexes, loads, and allocation of one cell at `L0`. -/
def hd (L0 : Loc) (σ : HeapLang.State) : Exp → Option (Exp × HeapLang.State)
  | .app (.val (.rec_ f x e)) (.val v) => some ((e.subst f (.rec_ f x e)).subst x v, σ)
  | .rec_ f x e => some (.val (.rec_ f x e), σ)
  | .if (.val (.lit (.bool true))) e1 _ => some (e1, σ)
  | .if (.val (.lit (.bool false))) _ e2 => some (e2, σ)
  | .binop op (.val v1) (.val v2) => (op.eval v1 v2).map (fun v => (.val v, σ))
  | .unop op (.val v) => (op.eval v).map (fun v => (.val v, σ))
  | .load (.val (.lit (.loc l))) => match σ.get? l with | some (some v) => some (.val v, σ) | _ => none
  | .allocN (.val (.lit (.int n))) (.val v) =>
      if 0 < n ∧ n ≤ 1 ∧ σ.get? L0 = none then some (.val (.lit (.loc L0)), σ.initHeap L0 n v) else none
  | .pair (.val v1) (.val v2) => some (.val (.pair v1 v2), σ)
  | .fst (.val (.pair v1 _)) => some (.val v1, σ)
  | .snd (.val (.pair _ v2)) => some (.val v2, σ)
  | .cmpXchg (.val (.lit (.loc l))) (.val v1) (.val v2) => match σ.get? l with
    | some (some vl) => if vl.compareSafe v1 = true then
        some (.val (.pair vl (.lit (.bool (decide (vl = v1))))), if decide (vl = v1) then σ.initHeap l 1 v2 else σ) else none
    | _ => none
  | _ => none

def step1 (L0 : Loc) (σ : HeapLang.State) (e : Exp) : Option (Exp × HeapLang.State) :=
  let p := dc e
  if fill p.1 p.2 = e then (hd L0 σ p.2).map (fun q => (fill p.1 q.1, q.2)) else none

def runN (L0 : Loc) : Nat → Exp → HeapLang.State → Exp × HeapLang.State
  | 0, e, σ => (e, σ)
  | n+1, e, σ => match step1 L0 σ e with | some q => runN L0 n q.1 q.2 | none => (e, σ)

theorem ip1 {α : Type} {R : α → α → Prop} {a b : α} (h : Relation.Iterate R 1 a b) : R a b := by
  cases h with | tail y h1 h2 => cases h1; exact h2

theorem pp_prim {r r' : Exp} (σ : HeapLang.State) (h : Language.PurePrimStep r r') :
    PrimStep.primStep (r, σ) [] (r', σ, []) := by
  obtain ⟨e2, σ2, et, hs⟩ := h.safe σ
  obtain ⟨-, rfl, rfl, rfl⟩ := h.deterministic hs
  exact hs

theorem hd_sound {L0 : Loc} {σ σ' : HeapLang.State} {r r' : Exp} (h : hd L0 σ r = some (r', σ')) :
    PrimStep.primStep (r, σ) [] (r', σ', []) := by
  unfold hd at h
  split at h
  · cases h; exact pp_prim σ (ip1 (instPureExecBeta.pureExec trivial))
  · cases h; exact pp_prim σ (ip1 (instPureExecRec.pureExec trivial))
  · cases h; exact pp_prim σ (ip1 (instPureExecIfTrue.pureExec trivial))
  · cases h; exact pp_prim σ (ip1 (instPureExecIfFalse.pureExec trivial))
  · rename_i op v1 v2
    cases hh : op.eval v1 v2 <;> simp only [hh, Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact pp_prim σ (ip1 ((instPureExecBinOp (op := op) (v1 := v1) (v2 := v2)).pureExec hh))
  · rename_i op v
    cases hh : op.eval v <;> simp only [hh, Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact pp_prim σ (ip1 ((instPureExecUnOp (op := op) (v := v)).pureExec hh))
  · split at h
    · cases h; exact primStep_of_baseStep (.loadS _ _ _ ‹_›)
    · cases h
  · rename_i n v
    split at h
    · rename_i hc
      obtain ⟨h1, h2, h3⟩ := hc
      cases h
      refine primStep_of_baseStep (.allocNS n v σ L0 h1 (fun i hi0 hin => ?_))
      have : i = 0 := by omega
      subst this; simpa [loc_add_zero] using h3
    · cases h
  · cases h; exact pp_prim σ (ip1 (instPureExecPair.pureExec trivial))
  · cases h; exact pp_prim σ (ip1 (instPureExecFst.pureExec trivial))
  · cases h; exact pp_prim σ (ip1 (instPureExecSnd.pureExec trivial))
  · split at h
    · split at h
      · cases h; exact primStep_of_baseStep (.cmpXchgS _ _ _ _ _ _ ‹_› ‹_› rfl)
      · cases h
    · cases h
  · cases h

theorem step1_sound {L0 : Loc} {σ σ' : HeapLang.State} {e e' : Exp} (h : step1 L0 σ e = some (e', σ')) :
    PrimStep.primStep (e, σ) [] (e', σ', []) := by
  dsimp only [step1] at h
  split at h
  · rename_i hf
    cases hh : hd L0 σ (dc e).2 with
    | none => simp only [hh, Option.map_none, reduceCtorEq] at h
    | some q =>
      simp only [hh, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have := fill_primStep (dc e).1 (hd_sound (r' := q.1) (σ' := q.2) hh)
      rw [hf] at this; exact this
  · cases h

theorem runN_sound (L0 : Loc) : ∀ n e σ, Relation.ReflTransGen Language.ErasedStep ([e], σ) ([(runN L0 n e σ).1], (runN L0 n e σ).2)
  | 0, e, σ => .refl
  | n+1, e, σ => by
    unfold runN; split
    · rename_i q h
      exact .head ⟨[], Language.Step.of_primStep (step1_sound (e' := q.1) (σ' := q.2) h) (t₁ := []) (t₂ := [])⟩ (runN_sound L0 n q.1 q.2)
    · exact .refl

theorem irr_fill (K : List ECtxItem) {r : Exp} {σ : HeapLang.State} (hv : toVal r = none)
    (hirr : PrimStep.Irreducible (r, σ)) : PrimStep.Irreducible (fill K r, σ) := by
  intro obs e' σ' et hs
  obtain ⟨e2, -, hs2⟩ := Language.Context.primStep_fill_inv (K := fill K) hv hs
  exact hirr _ _ _ _ hs2
end T1c3

namespace T1c3
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

/-- A program that runs (by `runN`: pure steps, loads, one-cell allocation at `L0`) into a stuck redex has no safe WP. -/
theorem run_stuck (L0 : Loc) (e : Exp) (σ σ' : HeapLang.State) (n : Nat) (r : Exp)
    (hσ : (runN L0 n e σ).2 = σ') (hr : (dc (runN L0 n e σ).1).2 = r)
    (hf : fill (dc (runN L0 n e σ).1).1 r = (runN L0 n e σ).1) (hv : toVal r = none)
    (hirr : PrimStep.Irreducible (r, σ'))
    (Hwp : ∀ [HeapLangGS .hasLC HeapLangS], ⊢ iprop(BI.bigSepM (M := HeapF) (fun l v => pointsTo l (DFrac.own 1) v) σ.heap -∗ WP e {{ _r, True }})) :
    False := by
  have had := adeqP e σ (fun _ => True) Hwp
  rcases had.adequate_not_stuck [(runN L0 n e σ).1] _ _ rfl (runN_sound L0 n e σ) (List.mem_singleton_self _) with h | ⟨obs, e', σ'', efs, hs⟩
  · rw [← hf] at h; simp [EctxItemLanguage.fill_not_val hv] at h
  · rw [← hf, hσ] at hs; exact irr_fill _ hv hirr _ _ _ _ hs

theorem irr_of_base {e : Exp} {σ : HeapLang.State} (hsub : SubredexesAreValues e)
    (hb : ∀ κ e' σ' efs, ¬ BaseStep e σ κ e' σ' efs) : PrimStep.Irreducible (e, σ) :=
  fun _ _ _ _ hp => hb _ _ _ _ (baseStep_of_primStep hp hsub)
end T1c3

namespace T1c3
open Iris Iris.BI Iris.HeapLang Iris.Std Iris.ProgramLogic Language.Notation FromMathlib
open Iris.ProgramLogic.EctxLanguage Iris.ProgramLogic.EctxItemLanguage
/-- A program that runs (by `runN`) to the value `w` gives `φ w` from adequacy. -/
theorem run_val {L0 : Loc} {e : Exp} {σ : HeapLang.State} {n : Nat} {w : Val} {φ : Val → Prop}
    (had : adequate .NotStuck e σ (fun v _ => φ v)) (hw : (runN L0 n e σ).1 = .val w) : φ w :=
  had.adequate_result [] _ w (hw ▸ runN_sound L0 n e σ)
abbrev vZ : Val := .lit (.int 0)
abbrev σ1 (v : Val) : HeapLang.State :=
  { heap := PartialMap.singleton (M := HeapF) ⟨0⟩ (some v), usedProphId := ∅ }
theorem pts1 [HeapLangGS .hasLC HeapLangS] (v : Val) :
    BI.bigSepM (M := HeapF) (fun l v => pointsTo l (DFrac.own 1) v) (σ1 v).heap ⊢ pointsTo (⟨0⟩ : Loc) (DFrac.own 1) (some v) :=
  BI.BigSepM.bigSepM_singleton.1
end T1c3

namespace T1c3
open Iris Iris.BI Iris.HeapLang Iris.Std Iris.ProgramLogic Language.Notation FromMathlib
open Iris.ProgramLogic.EctxLanguage Iris.ProgramLogic.EctxItemLanguage
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
theorem step_one {e : Exp} {σ : HeapLang.State} (hirr : PrimStep.Irreducible (e, σ)) {o ρ}
    (hs : Language.Step ([e], σ) o ρ) : False := by
  generalize hb : ([e], σ) = b at hs
  cases hs with
  | atomic H t₁ t₂ =>
    have h1 := congrArg Prod.fst hb
    have h2 := congrArg Prod.snd hb
    simp only at h1 h2
    subst h2
    rcases t₁ with _ | ⟨a, t₁⟩
    · simp at h1; obtain ⟨rfl, rfl⟩ := h1; exact hirr _ _ _ _ H
    · simp at h1
theorem rtc_stuck {e : Exp} {σ : HeapLang.State} (hirr : PrimStep.Irreducible (e, σ)) {C}
    (h : Relation.ReflTransGen Language.ErasedStep ([e], σ) C) : C = ([e], σ) := by
  induction h with
  | refl => rfl
  | tail _ hs ih => subst ih; obtain ⟨_, hs⟩ := hs; exact (step_one hirr hs).elim
theorem rtc_from_val {v : Val} {e : Exp} (h : Relation.ReflTransGen Language.PurePrimStep (Exp.val v) e) :
    e = .val v := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    subst ih
    obtain ⟨e', σ', et, hp⟩ := hs.safe (default : HeapLang.State)
    have := Language.val_stuck hp
    simp at this
abbrev vU : Val := .lit .unit
abbrev eR : Exp := .resolve (.val vU) (.val vU) (.val vU)
end T1c3

namespace T1c3
open Iris Iris.BI Iris.HeapLang Iris.Std Iris.ProgramLogic Language.Notation FromMathlib
open Iris.ProgramLogic.EctxLanguage Iris.ProgramLogic.EctxItemLanguage
abbrev fU : Val := .rec_ .anon .anon (.val (.lit .unit))
theorem arr1v [HeapLangGS .hasLC HeapLangS] (v : Val) :
    pointsTo (⟨0⟩:Loc) (DFrac.own 1) (some v) ⊢ array (⟨0⟩:Loc) (DFrac.own 1) [v] := array_singleton.2
theorem σ1_none (v : Val) (k : Int) (hk : k ≠ 0) : (σ1 v).get? ⟨k⟩ = none := by
  simp [State.get?, PartialMap.singleton, LawfulPartialMap.get?_insert, get?_empty]; omega
/-- allocN(#0, v) is stuck. -/
theorem alloc0_irr (σ : HeapLang.State) (v : Val) : PrimStep.Irreducible (Exp.allocN (.val (.lit (.int 0))) (.val v), σ) :=
  irr_of_base (subredexes_are_values fun Ki e' heq => by cases Ki <;> cases heq <;> rfl)
    (fun _ _ _ _ hb => by cases hb; omega)


-- `Iris.HeapLang.wp_array_free` idx 8: necessary
theorem t1c3_1 : ¬ drop0% Iris.HeapLang.wp_array_free 8 := fun h => by
  refine run_stuck ⟨0⟩ hl(&arrayFree #(⟨0⟩:Loc) #(1:Int)) default default 10 (.free (.val (.lit (.loc ⟨0⟩)))) rfl rfl rfl rfl
    (irr_of_base (subredexes_are_values fun Ki e' heq => by cases Ki <;> cases heq <;> rfl)
      (fun _ _ _ _ hb => by cases hb <;> simp_all [State.get?, default, get?_empty])) ?_
  intro inst; iintro -
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (vs := []) (n := 1))
  · iapply array_nil.2; itrivial
  · inext; iintro -; itrivial

-- `Iris.HeapLang.wp_array_copy_to` idx 11: necessary
theorem t1c3_2 : ¬ drop0% Iris.HeapLang.wp_array_copy_to 11 := fun h => by
  refine run_stuck ⟨0⟩ hl(&arrayCopyTo #(⟨1⟩:Loc) #(⟨0⟩:Loc) #(1:Int)) (σ1 vU) (σ1 vU) 8
    (.store (.val (.lit (.loc ⟨1⟩))) (.val vU)) rfl rfl rfl rfl
    (irr_of_base (subredexes_are_values fun Ki e' heq => by cases Ki <;> cases heq <;> rfl)
      (fun _ _ _ _ hb => by cases hb; rename_i hg; rw [σ1_none _ 1 (by decide)] at hg; cases hg)) ?_
  intro inst; iintro HP
  ihave HP := pts1 _ $$ HP
  ihave HP := arr1v _ $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (dst := ⟨1⟩) (src := ⟨0⟩) (vdst := []) (vsrc := [vU]) (dq := DFrac.own 1) (n := 1) rfl) $$ [HP]
  · isplitl []
    · iapply array_nil.2; itrivial
    · iexact HP
  · inext; iintro -; itrivial

-- `Iris.HeapLang.wp_array_copy_to` idx 12: necessary
theorem t1c3_3 : ¬ drop0% Iris.HeapLang.wp_array_copy_to 12 := fun h => by
  refine run_stuck ⟨0⟩ hl(&arrayCopyTo #(⟨0⟩:Loc) #(⟨1⟩:Loc) #(1:Int)) (σ1 vU) (σ1 vU) 7
    (.load (.val (.lit (.loc ⟨1⟩)))) rfl rfl rfl rfl
    (irr_of_base (subredexes_are_values fun Ki e' heq => by cases Ki <;> cases heq <;> rfl)
      (fun _ _ _ _ hb => by cases hb; rename_i hg; rw [σ1_none _ 1 (by decide)] at hg; cases hg)) ?_
  intro inst; iintro HP
  ihave HP := pts1 _ $$ HP
  ihave HP := arr1v _ $$ HP
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (dst := ⟨0⟩) (src := ⟨1⟩) (vdst := [vU]) (vsrc := []) (dq := DFrac.own 1) (n := 1) rfl) $$ [HP]
  · isplitr []
    · iexact HP
    · iapply array_nil.2; itrivial
  · inext; iintro -; itrivial

-- `Iris.HeapLang.wp_array_clone` idx 9: necessary
theorem t1c3_4 : ¬ drop0% Iris.HeapLang.wp_array_clone 9 := fun h => by
  refine run_stuck ⟨0⟩ hl(&arrayClone #(⟨5⟩:Loc) #(1:Int)) default ((default : HeapLang.State).initHeap ⟨0⟩ 1 (some vU)) 13
    (.load (.val (.lit (.loc ⟨5⟩)))) rfl rfl rfl rfl
    (irr_of_base (subredexes_are_values fun Ki e' heq => by cases Ki <;> cases heq <;> rfl)
      (fun _ _ _ _ hb => by
        cases hb; rename_i hg
        simp [State.get?, get?_foldl_insert, default, get?_empty, LawfulPartialMap.get?_insert] at hg)) ?_
  intro inst; iintro -
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨5⟩) (dq := DFrac.own 1) (vl := []) (n := 1) (by decide))
  · iapply array_nil.2; itrivial
  · inext; iintro %l -; itrivial

-- `Iris.HeapLang.wp_array_clone` idx 10: necessary
theorem t1c3_5 : ¬ drop0% Iris.HeapLang.wp_array_clone 10 := fun h => by
  refine run_stuck ⟨0⟩ hl(&arrayClone #(⟨5⟩:Loc) #(0:Int)) default default 3
    (.allocN (.val (.lit (.int 0))) (.val vU)) rfl rfl rfl rfl (alloc0_irr _ _) ?_
  intro inst; iintro -
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (s := .NotStuck) (E := ⊤) (l := ⟨5⟩) (dq := DFrac.own 1) (vl := []) (n := 0) rfl)
  · iapply array_nil.2; itrivial
  · inext; iintro %l -; itrivial

-- `Iris.HeapLang.wp_array_init_loop` idx 11: necessary
theorem t1c3_6 : ¬ drop0% Iris.HeapLang.wp_array_init_loop 11 := fun h => by
  refine run_stuck ⟨0⟩ hl(&arrayInitLoop #(⟨0⟩:Loc) #((0:Nat):Int) #(1:Int) &fU) default default 11
    (.store (.val (.lit (.loc ⟨0⟩))) (.val vU)) rfl rfl rfl rfl
    (irr_of_base (subredexes_are_values fun Ki e' heq => by cases Ki <;> cases heq <;> rfl)
      (fun _ _ _ _ hb => by cases hb; rename_i hg; simp [State.get?, default, get?_empty] at hg)) ?_
  intro inst; iintro -
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (Q := fun _ _ => iprop(True)) (s := .NotStuck) (E := ⊤) (l := ⟨0⟩) (i := 0) (k := 0) (n := 1) (f := fU))
  · isimp; isplitl []
    · iapply array_nil.2; itrivial
    · itrivial
  · inext; iintro %vs -; itrivial

-- `Iris.HeapLang.wp_array_init` idx 8: necessary
theorem t1c3_7 : ¬ drop0% Iris.HeapLang.wp_array_init 8 := fun h => by
  refine run_stuck ⟨0⟩ hl(&arrayInit #(0:Int) &fU) default default 3
    (.allocN (.val (.lit (.int 0))) (.val vU)) rfl rfl rfl rfl (alloc0_irr _ _) ?_
  intro inst; iintro -
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (Q := fun _ _ => iprop(True)) (s := .NotStuck) (E := ⊤) (n := 0) (f := fU))
  · isimp; first | itrivial | exact .rfl
  · inext; iintro %l %vs -; itrivial

-- `Iris.HeapLang.wp_array_init_fmap` idx 10: necessary
theorem t1c3_8 : ¬ drop0% Iris.HeapLang.wp_array_init_fmap 10 := fun h => by
  refine run_stuck ⟨0⟩ hl(&arrayInit #(0:Int) &fU) default default 3
    (.allocN (.val (.lit (.int 0))) (.val vU)) rfl rfl rfl rfl (alloc0_irr _ _) ?_
  intro inst; iintro -
  iapply (h (GF := HeapLangS) (hlc := .hasLC) (α := Unit) (g := fun _ => vU) (Q := fun _ _ => iprop(True)) (s := .NotStuck) (E := ⊤) (n := 0) (f := fU))
  · isimp; first | itrivial | exact .rfl
  · inext; iintro %l %vs -; itrivial
end T1c3

namespace T1c3
open Iris Iris.BI Iris.HeapLang Iris.Std Iris.ProgramLogic Language.Notation FromMathlib
open Iris.ProgramLogic.EctxLanguage Iris.ProgramLogic.EctxItemLanguage
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
-- `Iris.HeapLang.wp_baseCompletenessGoal` idx 6: necessary
theorem t1c3_9 : ¬ drop0% Iris.HeapLang.wp_baseCompletenessGoal 6 := fun h => by
  refine stuckM (GF := HeapLangS) (.var "a") default rfl (var_irr _) ?_
  intro inst; iintro - -
  iapply ((heapInv_default.trans (goal_wp (.var "a") default (var_irr _) (var_irr _) (@h .hasLC HeapLangS _ (.var "a") default ⊤))))
  all_goals first | itrivial | exact .rfl

theorem σ1_get0 (v : Val) : get? (M := HeapF) (σ1 v).heap (⟨0⟩ : Loc) = some (some v) := by
  simp [PartialMap.singleton, LawfulPartialMap.get?_insert]
theorem heapInv_σ1 {GF : BundledGFunctors} [HeapLangGS .hasLC GF] (v : Val) :
    ⊢ iprop(BI.bigSepM (M := HeapF) (fun l v => pointsTo l (DFrac.own 1) v) (σ1 v).heap -∗
      BI.bigSepM (M := HeapF) (fun l _ => metaToken l ⊤) (σ1 v).heap -∗ heapInv (GF := GF) (σ1 v)) := by
  iintro Hp Hm
  ihave Hp := BI.BigSepM.bigSepM_singleton.1 $$ Hp
  ihave Hm := BI.BigSepM.bigSepM_singleton.1 $$ Hm
  isplitl [Hp Hm]
  · iapply BI.BigSepM.bigSepM_singleton.2
    isplitl [Hp]
    · iexact Hp
    · iexact Hm
  · iapply BigSepS.bigSepS_empty.2; first | itrivial | exact .rfl
theorem atomic_var : Language.Atomic (State := HeapLang.State) Language.Atomicity.StronglyAtomic (Exp.var "a") :=
  ⟨fun hs => (var_irr _ _ _ _ _ hs).elim⟩

-- `Iris.HeapLang.wp_base_atomic_nochange` idx 9: removable
theorem t1c3_10 : drop% Iris.HeapLang.wp_base_atomic_nochange 9 := by
  intro hlc GF inst e₁ v₂ l vlive σ E hcell hbase hdet
  exact Iris.HeapLang.wp_base_atomic_nochange l vlive σ E
    (base_step_to_val_atomic .StronglyAtomic (hbase σ hcell)) hcell hbase hdet

-- `Iris.HeapLang.wp_base_atomic` idx 10: removable
theorem t1c3_11 : drop% Iris.HeapLang.wp_base_atomic 10 := by
  intro hlc GF inst e₁ v₂ l vlive vnew σ E hcell hbase hdet
  exact Iris.HeapLang.wp_base_atomic l vlive vnew σ E
    (base_step_to_val_atomic .StronglyAtomic (hbase σ hcell)) hcell hbase hdet

-- `Iris.HeapLang.wp_base_atomic_nochange` idx 10: necessary
theorem t1c3_12 : ¬ drop0% Iris.HeapLang.wp_base_atomic_nochange 10 := fun h => by
  refine stuckM (GF := HeapLangS) (.load (.val (.lit (.loc ⟨0⟩)))) default rfl load0_irr ?_
  intro inst; iintro - -
  iapply (heapInv_default.trans (goal_wp _ default load0_irr load0_irr
    (@h .hasLC HeapLangS _ (.load (.val (.lit (.loc ⟨0⟩)))) vU ⟨0⟩ vU default ⊤
      (base_step_to_val_atomic .StronglyAtomic (BaseStep.loadS ⟨0⟩ vU (σ1 vU) (σ1_get0 vU)))
      (fun σ'' hg => .loadS _ _ _ hg) (fun hg hs => loadS_det hg hs))))
  all_goals first | itrivial | exact .rfl

-- `Iris.HeapLang.wp_base_atomic` idx 11: necessary
theorem t1c3_13 : ¬ drop0% Iris.HeapLang.wp_base_atomic 11 := fun h => by
  refine stuckM (GF := HeapLangS) (.load (.val (.lit (.loc ⟨0⟩)))) default rfl load0_irr ?_
  intro inst; iintro - -
  iapply (heapInv_default.trans (goal_wp _ default load0_irr load0_irr
    (@h .hasLC HeapLangS _ (.load (.val (.lit (.loc ⟨0⟩)))) vU ⟨0⟩ vU (some vU) default ⊤
      (base_step_to_val_atomic .StronglyAtomic (BaseStep.loadS ⟨0⟩ vU (σ1 vU) (σ1_get0 vU)))
      (fun σ'' hg => by rw [State.initHeap_self hg]; exact .loadS _ _ _ hg)
      (fun hg hs => by
        obtain ⟨ho, he, hσ, hf⟩ := loadS_det hg hs
        exact ⟨ho, he, hσ.trans (State.initHeap_self hg).symm, hf⟩))))
  all_goals first | itrivial | exact .rfl

-- `Iris.HeapLang.wp_base_atomic_nochange` idx 11: necessary
theorem t1c3_14 : ¬ drop0% Iris.HeapLang.wp_base_atomic_nochange 11 := fun h => by
  refine stuckM (GF := HeapLangS) (.var "a") (σ1 vU) rfl (var_irr _) ?_
  intro inst; iintro Hp Hm
  ihave Hinv := heapInv_σ1 vU $$ Hp Hm
  iapply (goal_wp (.var "a") (σ1 vU) (var_irr _) (var_irr _)
    (@h .hasLC HeapLangS _ (.var "a") vU ⟨0⟩ vU (σ1 vU) ⊤ atomic_var (σ1_get0 vU) (fun _ hs => by cases hs)))
  iexact Hinv

-- `Iris.HeapLang.wp_base_atomic` idx 12: necessary
theorem t1c3_15 : ¬ drop0% Iris.HeapLang.wp_base_atomic 12 := fun h => by
  refine stuckM (GF := HeapLangS) (.var "a") (σ1 vU) rfl (var_irr _) ?_
  intro inst; iintro Hp Hm
  ihave Hinv := heapInv_σ1 vU $$ Hp Hm
  iapply (goal_wp (.var "a") (σ1 vU) (var_irr _) (var_irr _)
    (@h .hasLC HeapLangS _ (.var "a") vU ⟨0⟩ vU none (σ1 vU) ⊤ atomic_var (σ1_get0 vU) (fun _ hs => by cases hs)))
  iexact Hinv
end T1c3

namespace T1c3
open Iris Iris.BI Iris.HeapLang Iris.Std Iris.ProgramLogic Language.Notation FromMathlib
open Iris.ProgramLogic.EctxLanguage Iris.ProgramLogic.EctxItemLanguage
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
end T1c3

namespace T1c3
open Iris Iris.BI Iris.HeapLang Iris.Std Iris.ProgramLogic Language.Notation FromMathlib
-- `Iris.HeapLang.wp_base_pure` idx 6: removable
theorem t1c3_16 : drop% Iris.HeapLang.wp_base_pure 6 := by
  intro hlc GF inst e₁ e₂ φ hφ σ E hbase
  exact @Iris.HeapLang.wp_base_pure hlc GF inst e₁ e₂ True (pe_of_base hbase) trivial σ E hbase

-- `Iris.HeapLang.wp_base_pure` idx 7: removable
theorem t1c3_17 : drop% Iris.HeapLang.wp_base_pure 7 := by
  intro hlc GF inst e₁ e₂ φ hpe σ E hbase
  exact @Iris.HeapLang.wp_base_pure hlc GF inst e₁ e₂ True (pe_of_base hbase) trivial σ E hbase

-- `Iris.HeapLang.wp_base_pure` idx 10: removable
theorem t1c3_18 : drop% Iris.HeapLang.wp_base_pure 10 := by
  intro hlc GF inst e₁ e₂ φ hpe hφ σ E
  iintro Hinv
  imodintro
  iright
  iframe Hinv
  iintro %Φ %E₂ H
  iapply wp_pure_step_later (Hexec := hpe) (Hφ := hφ)
  iintro !> -
  ihave Htraj : iprop(∀ σ₁, heapInv σ₁ ={E}=∗
      ∃ κ σ₁', ⌜PrimSteps e₁ σ₁ κ e₂ σ₁' []⌝ ∗ heapInv σ₁') $$ []
  · iintro %σ₁ Hinv₁
    imodintro
    iexists [], σ₁
    iframe Hinv₁
    ipureintro
    exact PrimSteps.once (pp_prim σ₁ (ip1 (hpe.pureExec hφ)))
  iapply fupd_wp
  imod H $$ Htraj with ⟨Hwp, _⟩
  imodintro
  iexact Hwp
-- `Iris.HeapLang.wp_base_atomic_nochange` idx 12: removable
theorem t1c3_19 : drop% Iris.HeapLang.wp_base_atomic_nochange 12 := by
  intro hlc GF inst e₁ v₂ l vlive σ E hatom hcell hbase
  exact Iris.HeapLang.wp_base_atomic_nochange l vlive σ E hatom hcell hbase
    (fun hg hs => det2 (hbase _ hg) hs (Or.inl rfl))

-- `Iris.HeapLang.wp_base_atomic` idx 13: removable
theorem t1c3_20 : drop% Iris.HeapLang.wp_base_atomic 13 := by
  intro hlc GF inst e₁ v₂ l vlive vnew σ E hatom hcell hbase
  exact Iris.HeapLang.wp_base_atomic l vlive vnew σ E hatom hcell hbase
    (fun hg hs => det2 (hbase _ hg) hs (Or.inr ⟨l, vlive, vnew, hg, rfl⟩))
end T1c3

namespace T1c3
open Iris Iris.BI Iris.HeapLang Iris.Std Iris.ProgramLogic COFE
abbrev H0 : Type → Type := fun V => Std.ExtTreeMap Nat V compare
/-- HeapLangS plus a ghost-map slot (Nat ↦ Exp, for the thread-pool invariant) and a cancelable-invariant slot. -/
def GF2 : BundledGFunctors
  | 0 => ⟨InvMapF⟩
  | 1 => ⟨constOF CoPsetDisjL⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet)⟩
  | 3 => ⟨Auth.AuthURF (constOF Credit)⟩
  | 4 => ⟨constOF (HeapView Loc (Agree (DiscreteO (Option Val))) HeapF)⟩
  | 5 => ⟨constOF (HeapView Loc (Agree (DiscreteO GName)) HeapF)⟩
  | 6 => ⟨constOF MetaUR⟩
  | 7 => ⟨constOF (HeapView ProphId (Agree (DiscreteO (List (Val × Val)))) ProphMapF)⟩
  | 8 => ⟨constOF (Auth (InvHeapMapUR (Option Val) HeapF))⟩
  | 9 => ⟨constOF (HeapView Nat (Agree (DiscreteO Exp)) H0)⟩
  | 10 => ⟨CInvF⟩
  | _ => ⟨constOF Unit⟩
instance preGF2 : HeapLangGpreS HasLC.hasLC GF2 where
  toWsatGpreS := by
    constructor
    · exists 0
    · exists 1
    · exists 2
  toLcGpreS := by
    constructor
    · exists 3
  heap_pre := by
    constructor
    · constructor
      exists 4
    · constructor
      exists 5
    · exists 6
  proph_pre := by
    constructor
    · constructor
      exists 7
  inv_heap_pre := by
    constructor
    exists 8
instance gmGF2 : GhostMapG GF2 Nat Exp H0 := { elem := { τ := 9, transp := rfl } }
instance ciGF2 : CInvG GF2 := { inv := { τ := 10, transp := rfl } }
end T1c3

namespace T1c3
open Iris Iris.BI Iris.HeapLang Iris.Std Iris.ProgramLogic Language.Notation FromMathlib
-- `Iris.HeapLang.heap_lang_sem_completeness` idx 10: necessary
theorem t1c3_21 : ¬ drop0% Iris.HeapLang.heap_lang_sem_completeness 10 := fun h => by
  have had := Iris.HeapLang.heap_adequacy (GF := GF2) (.val vU) default (fun _ => False) (fun {_} => by
    iintro -
    iapply (@h .hasLC GF2 _ H0 _ _ _ (.val vU) default (fun _ => False))
    iapply heapInv_default)
  exact had.adequate_result [] default vU .refl

-- `Iris.HeapLang.heap_lang_sem_completeness_nofork` idx 10: necessary
theorem t1c3_22 : ¬ drop0% Iris.HeapLang.heap_lang_sem_completeness_nofork 10 := fun h => by
  have had := Iris.HeapLang.heap_adequacy (GF := GF2) (.val vU) default (fun _ => False) (fun {_} => by
    iintro -
    iapply (wp_mono (fun v => BI.exists_elim fun σ' => BI.sep_elim_right))
    iapply (@h .hasLC GF2 _ H0 _ _ _ (.val vU) default (fun _ _ => False))
    iapply heapInv_default)
  exact had.adequate_result [] default vU .refl
end T1c3

namespace T1c3
open Iris Iris.BI Iris.HeapLang Iris.Std Iris.ProgramLogic Language.Notation FromMathlib
-- `_private.Iris.HeapLang.Lib.Counter.0.Iris.HeapLang.Counter.incr_spec` idx 8: necessary
theorem t1c3_23 : ¬ drop0% _private.Iris.HeapLang.Lib.Counter.«0».Iris.HeapLang.Counter.incr_spec 8 := fun h => by
  have had := adeqP hl(&Counter.incr #(⟨0⟩:Loc)) (σ1 vZ) (fun _ => False) (fun {_} => by
    iintro HP
    ihave Hl := pts1 _ $$ HP
    imod inv_alloc nroot ⊤ (Counter.counterInv (fun _ => iprop(True)) ⟨0⟩) $$ [Hl] with #Hinv
    · inext; iexists 0; iframe
    iapply (h (hlc := .hasLC) (GF := HeapLangS) (N := nroot) (A := fun _ => iprop(True)) iprop(True) iprop(False) ⟨0⟩)
    · isplit
      · iexact Hinv
      · itrivial
    · inext; iintro HF; iexact HF)
  exact run_val (L0 := ⟨0⟩) (n := 40) had rfl

-- `_private.Iris.HeapLang.Lib.Counter.0.Iris.HeapLang.Counter.read_spec` idx 8: necessary
theorem t1c3_24 : ¬ drop0% _private.Iris.HeapLang.Lib.Counter.«0».Iris.HeapLang.Counter.read_spec 8 := fun h => by
  have had := adeqP hl(&Counter.read #(⟨0⟩:Loc)) (σ1 vZ) (fun _ => False) (fun {_} => by
    iintro HP
    ihave Hl := pts1 _ $$ HP
    imod inv_alloc nroot ⊤ (Counter.counterInv (fun _ => iprop(True)) ⟨0⟩) $$ [Hl] with #Hinv
    · inext; iexists 0; iframe
    iapply (h (hlc := .hasLC) (GF := HeapLangS) (N := nroot) (A := fun _ => iprop(True)) iprop(True) (fun _ => iprop(False)) ⟨0⟩)
    · isplit
      · iexact Hinv
      · itrivial
    · inext; iintro %c HF; iexact HF)
  exact run_val (L0 := ⟨0⟩) (n := 40) had rfl
end T1c3

namespace T1c3
open Iris Iris.BI Iris.HeapLang Iris.Std Iris.ProgramLogic Language.Notation FromMathlib
open Iris.ProgramLogic.EctxLanguage Iris.ProgramLogic.EctxItemLanguage
-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.erasure_cut` idx 3: necessary
theorem t1c3_25 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.erasure_cut 3 := fun h => by
  have hirr : PrimStep.Irreducible (eR, (default : HeapLang.State)) :=
    res_irr _ _ _ _ (fun _ _ _ _ hb => by cases hb) (fun Ki x h => by cases Ki <;> simp [ECtxItem.fill] at h)
  obtain ⟨t2, σ2, hos, -, hpr⟩ := h (e := eR) (σ := default) (φ := fun _ _ => True)
    (runN_sound ⟨0⟩ 10 (Iris.HeapLang.eraseExpr eR) (Iris.HeapLang.eraseState default))
  have hc := rtc_stuck hirr hos
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  have hv : (runN ⟨0⟩ 10 (Iris.HeapLang.eraseExpr eR) (Iris.HeapLang.eraseState default)).1 = .val vU := rfl
  simp only [hv] at hpr
  have h1 := (List.forall₂_cons.1 hpr).1
  have h2 := rtc_from_val h1
  simp [Iris.HeapLang.eraseExpr, eraseResolve] at h2
end T1c3

namespace T1c3
open Iris Iris.BI Iris.HeapLang Iris.Std Iris.ProgramLogic Language.Notation FromMathlib
open Iris.ProgramLogic.EctxLanguage Iris.ProgramLogic.EctxItemLanguage
/-- The diverging function `rec f x := f x`. -/
abbrev loopV : Val := .rec_ (.named "f") (.named "x") (.app (.var "f") (.var "x"))
/-- The continuation `λ _, a` with a free variable: stuck after one beta step. -/
abbrev kV : Val := .rec_ .anon .anon (.var "a")
theorem loop_wp [HeapLangGS .hasLC HeapLangS] (v : Val) (Ψ : Val → IProp HeapLangS) :
    ⊢ (iprop(WP hl(&loopV &v) {{ Ψ }}) : IProp HeapLangS) := by
  iloeb as IH
  wp_rec
  iexact IH
theorem qp_ne : ¬ ((1 : Qp) + 1 = 1) := fun h => by
  have h2 := congrArg Subtype.val h
  grind
/-- Φ q := ⌜q = 1 + 1⌝ is not fractional. -/
abbrev phiB (q : Qp) : IProp HeapLangS := iprop(⌜q = 1 + 1⌝)
/-- A lawful RwLock whose lock predicate records (under a later) one instance of fractionality of Φ;
acquiring diverges and the locked tokens are False. -/
abbrev rwT [HeapLangGS .hasLC HeapLangS] : RwLock (hlc := .hasLC) HeapLangS where
  newlock := fU
  acquireReader := loopV
  releaseReader := fU
  acquireWriter := loopV
  releaseWriter := fU
  rwlockG := fun _ => Unit
  name := Unit
  isRwLock _ _ _ Φ := iprop(▷ □ (Φ (1 + 1) -∗ Φ 1 ∗ Φ 1))
  readerLocked _ _ _ := iprop(False)
  writerLocked _ _ := iprop(False)
  isRwLock_persistent _ _ _ := by infer_instance
  isRwLock_iff _ _ Φ Ψ := by
    iintro #H #Heq
    inext
    imodintro
    iintro HΨ
    icases Heq $$ %(1 + 1) with ⟨_, Hb⟩
    ihave HΦ := Hb $$ HΨ
    icases H $$ HΦ with ⟨H1, H2⟩
    icases Heq $$ %1 with ⟨Ha1, _⟩
    icases Heq $$ %1 with ⟨Ha2, _⟩
    isplitl [H1]
    · iapply Ha1; iexact H1
    · iapply Ha2; iexact H2
  readerLocked_timeless _ _ := by infer_instance
  writerLocked_timeless _ := by infer_instance
  writerLocked_exclusive _ := BI.sep_elim_left
  writerLocked_not_readerLocked _ _ := BI.sep_elim_left
  newlock_spec := by
    intro L Φ P ioΦ ioq inst
    iintro %Φ' HP HΦ'
    wp_rec
    iapply (wp_value' (Φ := Φ') (v := Val.lit .unit))
    iapply HΦ' $$ %(Val.lit .unit) %()
    iintro !> !> HΦ
    iapply (inst.as_fractional_fractional.fractional 1 1).1
    iexact HΦ
  acquireReader_spec _ lk _ := by
    iintro %Φ' _ _
    iapply loop_wp
  releaseReader_spec _ _ _ _ := by
    iintro %Φ' ⟨_, HF, _⟩ _
    iexfalso; iexact HF
  acquireWriter_spec _ lk _ := by
    iintro %Φ' _ _
    iapply loop_wp
  releaseWriter_spec _ _ _ := by
    iintro %Φ' ⟨_, HF, _⟩ _
    iexfalso; iexact HF
end T1c3

namespace T1c3
open Iris Iris.BI Iris.HeapLang Iris.Std Iris.ProgramLogic Language.Notation FromMathlib
open Iris.ProgramLogic.EctxLanguage Iris.ProgramLogic.EctxItemLanguage
-- `Iris.HeapLang.RwLock.newlock_spec` idx 9: necessary
theorem t1c3_26 : ¬ drop0% Iris.HeapLang.RwLock.newlock_spec 9 := fun h => by
  refine run_stuck ⟨0⟩ hl(&kV (&fU #())) default default 5 (.var "a") rfl rfl rfl rfl (var_irr _) ?_
  intro inst
  refine BI.wand_intro (BI.sep_elim_left.trans ?_)
  refine .trans ?_ (@wp_bind _ _ _ _ _ _ _ _ (fun e => Exp.app (.val kV) e) (instContextFill [ECtxItem.appR (.val kV)]) _ _ _ _)
  iintro -
  iapply (@h .hasLC HeapLangS heapLangInst rwT () phiB iprop(True) .in .in)
  · itrivial
  · inext
    iintro %lk %γ H
    iapply (wp_pure_step_later (Hexec := instPureExecBeta (f := .anon) (x := .anon) (e := .var "a") (v := lk))
      (Hφ := trivial) (s := .NotStuck) (E := ⊤) (Φ := fun _ => iprop(True)))
    iintro !> -
    icases H $$ [] with ⟨%h1, _⟩
    · ipureintro; rfl
    exact (qp_ne h1.symm).elim
end T1c3

namespace T1c3
open Iris Iris.BI Iris.HeapLang Iris.Std Iris.ProgramLogic COFE
/-- HeapLangS plus a RwSpinLock ghost slot. -/
def GF3 : BundledGFunctors
  | 0 => ⟨InvMapF⟩
  | 1 => ⟨constOF CoPsetDisjL⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet)⟩
  | 3 => ⟨Auth.AuthURF (constOF Credit)⟩
  | 4 => ⟨constOF (HeapView Loc (Agree (DiscreteO (Option Val))) HeapF)⟩
  | 5 => ⟨constOF (HeapView Loc (Agree (DiscreteO GName)) HeapF)⟩
  | 6 => ⟨constOF MetaUR⟩
  | 7 => ⟨constOF (HeapView ProphId (Agree (DiscreteO (List (Val × Val)))) ProphMapF)⟩
  | 8 => ⟨constOF (Auth (InvHeapMapUR (Option Val) HeapF))⟩
  | 9 => ⟨Iris.HeapLang.RwSpinLock.RwSpinLockF⟩
  | _ => ⟨constOF Unit⟩
instance preGF3 : HeapLangGpreS HasLC.hasLC GF3 where
  toWsatGpreS := by
    constructor
    · exists 0
    · exists 1
    · exists 2
  toLcGpreS := by
    constructor
    · exists 3
  heap_pre := by
    constructor
    · constructor
      exists 4
    · constructor
      exists 5
    · exists 6
  proph_pre := by
    constructor
    · constructor
      exists 7
  inv_heap_pre := by
    constructor
    exists 8
instance rwGF3 : Iris.HeapLang.RwSpinLock.RwSpinLockG GF3 := { elemG := { τ := 9, transp := rfl } }
end T1c3

namespace T1c3
open Iris Iris.BI Iris.HeapLang Iris.Std Iris.ProgramLogic Language.Notation FromMathlib
open Iris.ProgramLogic.EctxLanguage Iris.ProgramLogic.EctxItemLanguage
theorem adeqG {GF : BundledGFunctors} [HeapLangGpreS .hasLC GF] (e : Exp) (σ : HeapLang.State) (φ : Val → Prop)
    (Hwp : ∀ [HeapLangGS .hasLC GF], ⊢ iprop(BI.bigSepM (M := HeapF) (fun l v => pointsTo l (DFrac.own 1) v) σ.heap -∗ WP e {{ v, ⌜φ v⌝ }})) :
    adequate .NotStuck e σ (fun v _ => φ v) := by
  refine wp_adequacy (GF := GF) .NotStuck e σ φ ?_
  intro inst κs
  imod genHeap_init (GF := GF) (H := HeapF) σ.heap with ⟨%γh, ⟨Hh, Hpts, _⟩⟩
  imod invHeap_init Loc _ (GF := GF) (H := HeapF) (E:= ⊤) with ⟨%γi, >Hi⟩
  imod (ProphMap.init κs σ.usedProphId) with ⟨%Gproph, Hproph⟩
  letI instHeapLangGS : HeapLangGS .hasLC GF := ⟨γh, Gproph, γi⟩
  imodintro
  iexists (fun σ κs => iprop% Iris.genHeapInterp σ.heap ∗ Iris.prophMapInterp κs σ.usedProphId)
  iexists (fun _ => iprop(True))
  simp only []
  ihave Hwp := (@Hwp _) $$ Hpts
  iframe Hwp Hproph Hh
theorem run_stuckG {GF : BundledGFunctors} [HeapLangGpreS .hasLC GF] (L0 : Loc) (e : Exp) (σ σ' : HeapLang.State) (n : Nat) (r : Exp)
    (hσ : (runN L0 n e σ).2 = σ') (hr : (dc (runN L0 n e σ).1).2 = r)
    (hf : fill (dc (runN L0 n e σ).1).1 r = (runN L0 n e σ).1) (hv : toVal r = none)
    (hirr : PrimStep.Irreducible (r, σ'))
    (Hwp : ∀ [HeapLangGS .hasLC GF], ⊢ iprop(BI.bigSepM (M := HeapF) (fun l v => pointsTo l (DFrac.own 1) v) σ.heap -∗ WP e {{ _r, True }})) :
    False := by
  have had := adeqG e σ (fun _ => True) Hwp
  rcases had.adequate_not_stuck [(runN L0 n e σ).1] _ _ rfl (runN_sound L0 n e σ) (List.mem_singleton_self _) with h | ⟨obs, e', σ'', efs, hs⟩
  · rw [← hf] at h; simp [EctxItemLanguage.fill_not_val hv] at h
  · rw [← hf, hσ] at hs; exact irr_fill _ hv hirr _ _ _ _ hs
abbrev phi3 (q : Qp) : IProp GF3 := iprop(⌜q = 1 + 1⌝)
end T1c3

namespace T1c3
open Iris Iris.BI Iris.HeapLang Iris.Std Iris.ProgramLogic Language.Notation FromMathlib
open Iris.ProgramLogic.EctxLanguage Iris.ProgramLogic.EctxItemLanguage
-- `Iris.HeapLang.RwSpinLock.newlock_spec` idx 8: necessary
theorem t1c3_27 : ¬ drop0% Iris.HeapLang.RwSpinLock.newlock_spec 8 := fun h => by
  refine run_stuckG (GF := GF3) ⟨0⟩ hl(&kV (&RwSpinLock.newlock #())) default ((default : HeapLang.State).initHeap ⟨0⟩ 1 (some (.lit (.int 0)))) 10 (.var "a") rfl rfl rfl rfl (var_irr _) ?_
  intro inst
  refine BI.wand_intro (BI.sep_elim_left.trans ?_)
  refine .trans ?_ (@wp_bind _ _ _ _ _ _ _ _ (fun e => Exp.app (.val kV) e) (instContextFill [ECtxItem.appR (.val kV)]) _ _ _ _)
  iintro -
  iapply (h (hlc := .hasLC) (GF := GF3) (Φ := phi3) (P := iprop(True)) (ioΦ := .in) (ioq := .in))
  · itrivial
  · inext
    iintro %lk %γ H
    ihave H1 := (show RwSpinLock.isRwLock γ lk phi3 ⊢ iprop(▷ internalFractional phi3) from BI.sep_elim_left) $$ H
    iapply (wp_pure_step_later (Hexec := instPureExecBeta (f := .anon) (x := .anon) (e := .var "a") (v := lk))
      (Hφ := trivial) (s := .NotStuck) (E := ⊤) (Φ := fun _ => iprop(True)))
    iintro !> -
    ihave H2 := (show internalFractional phi3 ⊢ iprop(phi3 (1 + 1) -∗ phi3 1 ∗ phi3 1) from
      BI.intuitionistically_elim.trans ((BI.forall_elim 1).trans ((BI.forall_elim 1).trans BI.and_elim_l))) $$ H1
    icases H2 $$ [] with ⟨%h1, _⟩
    · ipureintro; rfl
    exact (qp_ne h1.symm).elim
end T1c3

namespace T1c3
open Iris Iris.BI Iris.HeapLang Iris.Std Iris.ProgramLogic Language.Notation FromMathlib ORA LeibnizMultiSet FiniteMultiSet
open Iris.ProgramLogic.EctxLanguage Iris.ProgramLogic.EctxItemLanguage
-- `_private.Iris.HeapLang.Lib.RwSpinLock.0.Iris.HeapLang.RwSpinLock.rwStateInv_readLocked` idx 10: necessary
theorem t1c3_28 : ¬ drop0% _private.Iris.HeapLang.Lib.RwSpinLock.«0».Iris.HeapLang.RwSpinLock.rwStateInv_readLocked 10 := fun h => by
  have had := adeqG (GF := GF3) hl(!#(⟨0⟩:Loc)) (σ1 (.lit (.int (-2)))) (fun v => v ≠ .lit (.int (-2))) (fun {_} => by
    iintro HP
    ihave Hl := BI.BigSepM.bigSepM_singleton.1 $$ HP
    imod iOwn_alloc (F := RwSpinLock.RwSpinLockF) (● LeibnizMultiSet.ofSet (∅ : RwSpinLock.ReaderFracs)) with ⟨%γ, Hγ⟩
    · exact Auth.auth_valid.mpr trivial
    ihave HR := (h (hlc := .hasLC) (GF := GF3) (γ := γ) (l := ⟨0⟩) (Φ := fun _ => iprop(True)) (z := -2) (q := 1)
      (g := ∅) (by rw [size_empty]; rfl) fold_empty) $$ [Hl Hγ]
    · isplitl [Hl]
      · iexact Hl
      · isplitl [Hγ]
        · iexact Hγ
        · itrivial
    icases HR with ⟨%z', Hl', (⟨%hz1, _⟩ | ⟨%hz2, _⟩)⟩
    · wp_load
      ipureintro; simp; omega
    · wp_load
      ipureintro; simp; omega)
  exact run_val (L0 := ⟨0⟩) (n := 3) had rfl rfl
end T1c3

namespace T1c3
open Iris Iris.BI Iris.HeapLang Iris.Std Iris.ProgramLogic Language.Notation FromMathlib ORA LeibnizMultiSet FiniteMultiSet
open Iris.ProgramLogic.EctxLanguage Iris.ProgramLogic.EctxItemLanguage
theorem half_ne : ¬ (Qp.half 1 = 1) := fun h => by
  have h2 := congrArg Subtype.val h
  simp [Qp.half] at h2
  grind
-- `_private.Iris.HeapLang.Lib.RwSpinLock.0.Iris.HeapLang.RwSpinLock.rwStateInv_readLocked` idx 12: necessary
theorem t1c3_30 : ¬ drop0% _private.Iris.HeapLang.Lib.RwSpinLock.«0».Iris.HeapLang.RwSpinLock.rwStateInv_readLocked 12 := fun h => by
  have had := adeqG (GF := GF3) hl(!#(⟨0⟩:Loc)) (σ1 (.lit (.int 0))) (fun v => v ≠ .lit (.int 0)) (fun {_} => by
    iintro HP
    ihave Hl := BI.BigSepM.bigSepM_singleton.1 $$ HP
    imod iOwn_alloc (F := RwSpinLock.RwSpinLockF) (● LeibnizMultiSet.ofSet (∅ : RwSpinLock.ReaderFracs)) with ⟨%γ, Hγ⟩
    · exact Auth.auth_valid.mpr trivial
    ihave HR := (h (hlc := .hasLC) (GF := GF3) (γ := γ) (l := ⟨0⟩) (Φ := phi3) (z := 0) (q := 1 + 1)
      (g := ∅) (by omega) (by rw [size_empty]; rfl)) $$ [Hl Hγ]
    · isplitl [Hl]
      · iexact Hl
      · isplitl [Hγ]
        · iexact Hγ
        · ipureintro; rfl
    icases HR with ⟨%z', Hl', (⟨%hz1, _⟩ | ⟨%hz2, %q', %g', _, %hsz, %hfd, %hq'⟩)⟩
    · wp_load
      ipureintro; simp; omega
    · wp_load
      ipureintro
      intro hv
      simp at hv
      subst hv
      have hg : g' = ∅ := size_eq_zero_iff.1 (by simpa using hsz)
      subst hg
      rw [fold_empty, hq'] at hfd
      exact qp_ne hfd)
  exact run_val (L0 := ⟨0⟩) (n := 3) had rfl rfl

-- `_private.Iris.HeapLang.Lib.RwSpinLock.0.Iris.HeapLang.RwSpinLock.rwStateInv_readLocked` idx 11: necessary
theorem t1c3_29 : ¬ drop0% _private.Iris.HeapLang.Lib.RwSpinLock.«0».Iris.HeapLang.RwSpinLock.rwStateInv_readLocked 11 := fun h => by
  have had := adeqG (GF := GF3) hl(!#(⟨0⟩:Loc)) (σ1 (.lit (.int 0))) (fun v => v ≠ .lit (.int 0)) (fun {_} => by
    iintro HP
    ihave Hl := BI.BigSepM.bigSepM_singleton.1 $$ HP
    imod iOwn_alloc (F := RwSpinLock.RwSpinLockF) (● LeibnizMultiSet.ofSet ({Qp.half 1} : RwSpinLock.ReaderFracs)) with ⟨%γ, Hγ⟩
    · exact Auth.auth_valid.mpr trivial
    ihave HR := (h (hlc := .hasLC) (GF := GF3) (γ := γ) (l := ⟨0⟩) (Φ := fun q => iprop(⌜q = Qp.half 1⌝)) (z := 0) (q := Qp.half 1)
      (g := {Qp.half 1}) (by omega) (by rw [fold_singleton]; exact Qp.half_add_half 1)) $$ [Hl Hγ]
    · isplitl [Hl]
      · iexact Hl
      · isplitl [Hγ]
        · iexact Hγ
        · ipureintro; rfl
    icases HR with ⟨%z', Hl', (⟨%hz1, _⟩ | ⟨%hz2, %q', %g', _, %hsz, %hfd, %hq'⟩)⟩
    · wp_load
      ipureintro; simp; omega
    · wp_load
      ipureintro
      intro hv
      simp at hv
      subst hv
      have hg : g' = ∅ := size_eq_zero_iff.1 (by simpa using hsz)
      subst hg
      rw [fold_empty] at hfd
      subst hfd
      exact half_ne hq'.symm)
  exact run_val (L0 := ⟨0⟩) (n := 3) had rfl rfl
end T1c3

namespace T1c3
open Iris Iris.BI Iris.HeapLang Iris.Std Iris.ProgramLogic Language.Notation FromMathlib
open Iris.ProgramLogic.EctxLanguage Iris.ProgramLogic.EctxItemLanguage
-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.resolve_fst_primStepMatched` idx 11: necessary
theorem t1c3_31 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.resolve_fst_primStepMatched 11 := fun h => by
  obtain ⟨_, _, _, _, _, hs, -⟩ := @h (.val vU) (.val vU) (.val vU) [.pairL vU, .fst] (.pair (.val vU) (.val vU))
    (.val (.pair vU vU)) default (eraseState default) [] [] (.pairS vU vU _) rfl
    (fun {K'} {e0} _ he0 hns0 => erased_primStep_primStep
      (by rw [he0]; exact fill_primStep K' (primStep_of_baseStep (.pairS vU vU _))) hns0)
  exact res_irr (.val vU) default vU vU (fun _ _ _ _ hb => by cases hb)
    (fun Ki x h => by cases Ki <;> simp [ECtxItem.fill] at h) _ _ _ _ hs
end T1c3

namespace T1c3
open Iris Iris.BI Iris.HeapLang Iris.Std Iris.ProgramLogic Language.Notation FromMathlib
/-- A HeapLangGS instance from any InvGS with arbitrary ghost names (enough for fupd-only arguments). -/
@[instance_reducible] def hlgs (I : InvGS_gen .hasNoLC HeapLangS) : HeapLangGS .hasNoLC HeapLangS :=
  @HeapLangGS.mk .hasNoLC HeapLangS I { heapName := default, metaName := default }
    { prophMapName := default } { invHeapName := default }
/-- If `▷▷False ⊢ |={⊤}=> False` held under every InvGS, Löb and plain-later commuting give `⊢ ▷ False`. -/
theorem ll_false (H : ∀ (_ : InvGS_gen .hasNoLC HeapLangS), (iprop(▷ ▷ False) : IProp HeapLangS) ⊢ iprop(|={⊤}=> ◇ False)) : False := by
  have L : ∀ (_ : InvGS_gen .hasNoLC HeapLangS), ⊢ (iprop(|={⊤}=> ▷ False) : IProp HeapLangS) := fun I =>
    BI.true_intro.trans (loeb_weak (P := iprop(|={⊤}=> ▷ False)) (fupd_plain_later.trans ((fupd_mono (later_mono except0_later)).trans
      ((fupd_mono (H I)).trans (fupd_trans.trans (fupd_mono (show iprop(◇ False) ⊢ iprop(▷ False) from BI.or_elim .rfl BI.false_elim)))))))
  have h1 : ⊢ (iprop(▷ False) : IProp HeapLangS) := fupd_soundness .hasNoLC 0 (E1 := ⊤) (E2 := ⊤) (fun I => BI.wand_intro (BI.sep_elim_left.trans (L I)))
  exact UPred.pure_soundness (UPred.later_soundness h1)

-- `_private.Iris.HeapLang.ProofMode.0.Iris.ProofMode.tac_wp_heap_op` idx 14: necessary
theorem t1c3_32 : ¬ drop0% _private.Iris.HeapLang.ProofMode.«0».Iris.ProofMode.tac_wp_heap_op 14 := fun h => by
  refine ll_false (fun I => ?_)
  letI := hlgs I
  refine (h (hlc := .hasNoLC) (GF := HeapLangS) (Δ := iprop(▷ ▷ False)) (Δ' := iprop(▷ False)) (Δ'' := iprop(▷ False))
    (P := iprop(True)) (P' := iprop(True)) (s := .NotStuck) (E := ⊤) (K := []) (e := .val vU) (r := vU)
    (Φ := fun _ => iprop(◇ False)) ?_ .rfl ?_ ?_).trans wp_value_fupd'.1
  · iintro -
    iapply wp_value'
    isplitl []
    · ipureintro; rfl
    · itrivial
  · exact ⟨by iintro H; isplitl [H]; iexact H; itrivial, by iintro ⟨H, -⟩; iexact H⟩
  · exact BI.sep_elim_left.trans ((show iprop(▷ False) ⊢ iprop(◇ False) from BI.or_intro_l).trans
      (wp_value' (Φ := fun _ => iprop(◇ False)) (v := vU) (s := .NotStuck) (E := ⊤)))
end T1c3
