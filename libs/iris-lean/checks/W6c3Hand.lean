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
namespace W6c3
open Iris Iris.BI Iris.HeapLang Iris.ProgramLogic Iris.ProgramLogic.Language
open Iris.ProgramLogic.Language.Notation

abbrev HS := Iris.HeapLang.HeapLangS

theorem adeq_false (e : Exp) (σ σ' : HeapLang.State) (v : Val) (t : List Exp) (φ : Val → Prop)
    (hr : ([e], σ) -·->ₜₚ* (ToVal.ofVal v :: t, σ')) (hn : ¬ φ v)
    (H : ∀ [HeapLangGS .hasLC HS], ⊢ (WP e {{ w, ⌜φ w⌝ }} : IProp HS)) : False :=
  hn ((Iris.HeapLang.heap_adequacy (GF := HS) e σ φ fun {inst} => wand_intro (sep_elim_left.trans (@H inst))).adequate_result t σ' v hr)

theorem bstep {e e' : Exp} {σ σ' : HeapLang.State} {obs : List Observation} (h : BaseStep e σ obs e' σ' []) :
    ([e], σ) -·->ₜₚ* ([e'], σ') :=
  .single ⟨obs, by simpa using Step.of_primStep (t₁ := []) (t₂ := []) (EctxLanguage.primStep_of_baseStep h)⟩

def l0 : Loc := ⟨0⟩
def σ1 (v : Val) : HeapLang.State := (default : HeapLang.State).initHeap l0 1 (some v)
theorem σ1_get (v : Val) : (σ1 v).get? l0 = some (some v) := by rfl

abbrev i0 : Val := .lit (.int 0)
abbrev i1 : Val := .lit (.int 1)
theorem i01 : i0 ≠ i1 := by decide

theorem pe0 (e : Exp) : ProgramLogic.Language.PureExec True 0 e e := ⟨fun _ => by first | exact .refl | exact .refl _ | constructor⟩

theorem alloc_then (Ki : ECtxItem) (v : Val) (φ : Val → Prop) [HeapLangGS .hasLC HS]
    (H : ∀ l : Loc, (l ↦ some v : IProp HS) ⊢ WP (Ki.fill (ToVal.ofVal (Val.lit (.loc l)))) {{ w, ⌜φ w⌝ }}) :
    ⊢ (WP (Ki.fill hl(ref(v(&v)))) {{ w, ⌜φ w⌝ }} : IProp HS) := by
  refine .trans ?_ (wp_bind (ProgramLogic.fill [Ki]))
  refine .trans ?_ (wand_entails (true_intro.trans (wand_entails ((wp_alloc v).trans (forall_elim _)))))
  refine later_intro.trans (later_mono (forall_intro fun l => wand_intro ?_))
  exact (emp_sep.1.trans sep_elim_left).trans (H l)

theorem alloc_step (Ki : ECtxItem) (v : Val) :
    ([Ki.fill hl(ref(v(&v)))], (default : HeapLang.State)) -·->ₜₚ ([Ki.fill (ToVal.ofVal (Val.lit (.loc l0)))], σ1 v) := by
  have p : ((ProgramLogic.fill [Ki] hl(ref(v(&v))) : Exp), (default : HeapLang.State)) -<[]>->
      (ProgramLogic.fill [Ki] (ToVal.ofVal (Val.lit (.loc l0))), σ1 v, ([] : List Exp)) :=
    EctxLanguage.fill_primStep [Ki] (EctxLanguage.primStep_of_baseStep
      (BaseStep.allocNS 1 v default l0 (by decide) (fun _ _ _ => rfl)))
  have := Step.of_primStep (t₁ := []) (t₂ := []) p
  exact ⟨[], this⟩

theorem adeq_alloc (Ki : ECtxItem) (v : Val) (φ : Val → Prop) (σ' : HeapLang.State) (w : Val) (t : List Exp)
    (h2 : ([Ki.fill (ToVal.ofVal (Val.lit (.loc l0)))], σ1 v) -·->ₜₚ* (ToVal.ofVal w :: t, σ'))
    (hn : ¬ φ w)
    (H : ∀ [HeapLangGS .hasLC HS] (l : Loc), (l ↦ some v : IProp HS) ⊢ WP (Ki.fill (ToVal.ofVal (Val.lit (.loc l)))) {{ w, ⌜φ w⌝ }}) :
    False :=
  adeq_false (Ki.fill hl(ref(v(&v)))) default σ' w t φ (.head (alloc_step Ki v) h2) hn
    fun {_} => alloc_then Ki v φ H

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

abbrev efst : Exp := Exp.fst (ToVal.ofVal (Val.pair i0 i0))
abbrev ipair (a : Val) (b : Bool) : Val := Val.pair a (.lit (.bool b))

theorem hwp_fst [HeapLangGS .hasLC HS] :
    (iprop(▷ emp) : IProp HS) ⊢ WP efst {{ v', ⌜v' = i0⌝ ∗ emp }} :=
  ProofMode.tac_wp_pure (K := []) (Δ' := iprop(emp)) (n := 1) (e₂ := ToVal.ofVal i0) Iris.HeapLang.instPureExecFst trivial .rfl
    (emp_sep.2.trans ((sep_mono_left (pure_intro rfl)).trans (wp_value' (Φ := fun v' => iprop(⌜v' = i0⌝ ∗ emp)) (v := i0))))

theorem vpost [HeapLangGS .hasLC HS] (P : IProp HS) (w : Val) :
    P ⊢ WP (ToVal.ofVal w : Exp) {{ v, ⌜v = w⌝ }} :=
  (pure_intro rfl).trans (wp_value' (Φ := fun v => iprop(⌜v = w⌝)) (v := w))

theorem fstep : ([efst], (default : HeapLang.State)) -·->ₜₚ* ([ToVal.ofVal i0], default) := bstep (.fstS i0 i0 default)
theorem astep (v : Val) : ([hl(ref(v(&v)))], (default : HeapLang.State)) -·->ₜₚ* ([ToVal.ofVal (Val.lit (.loc l0))], σ1 v) :=
  bstep (.allocNS 1 v default l0 (by decide) (fun _ _ _ => rfl))

theorem stuck_adeq (e0 e : Exp) (σ0 σ : HeapLang.State) (φ : Val → Prop)
    (hr : ([e0], σ0) -·->ₜₚ* ([e], σ)) (hv : ToVal.toVal e = none)
    (hsr : EctxLanguage.SubredexesAreValues e) (hb : ∀ obs e' σ' efs, ¬ BaseStep e σ obs e' σ' efs)
    (H : ∀ [HeapLangGS .hasLC HS], ⊢ (WP e0 {{ w, ⌜φ w⌝ }} : IProp HS)) : False := by
  have ad := Iris.HeapLang.heap_adequacy (GF := HS) e0 σ0 φ fun {inst} => wand_intro (sep_elim_left.trans (@H inst))
  rcases ad.adequate_not_stuck [e] σ e rfl hr (List.mem_singleton_self _) with h | ⟨obs, e', σ', efs, hs⟩
  · rw [hv] at h; exact Bool.noConfusion h
  · exact hb _ _ _ _ (EctxLanguage.baseStep_of_primStep hs hsr)

abbrev vp : Val := Val.pair i0 i0
abbrev vq : Val := Val.pair i1 i1

theorem cx_sr (a b c : Val) : EctxLanguage.SubredexesAreValues (Exp.cmpXchg (.val a) (.val b) (.val c)) :=
  EctxItemLanguage.subredexes_are_values fun Ki e' h => by
    cases Ki <;> simp [fillItem, ECtxItem.fill] at h <;> first | rfl | (rcases h with ⟨rfl, -⟩; rfl) | (rcases h with ⟨-, rfl, -⟩; rfl) | (rcases h with ⟨-, -, rfl⟩; rfl) | (rcases h with ⟨-, rfl⟩; rfl)

theorem cx_nb (v1 v2 : Val) (h1 : vp.compareSafe v1 = false) (obs e' σ' efs) :
    ¬ BaseStep (Exp.cmpXchg (.val (.lit (.loc l0))) (.val v1) (.val v2)) (σ1 vp) obs e' σ' efs := by
  intro hs
  cases hs with
  | cmpXchgS _ _ _ vl _ _ hg hc _ =>
    rw [σ1_get] at hg; cases hg; rw [h1] at hc; exact Bool.noConfusion hc

theorem an_sr (a b : Val) : EctxLanguage.SubredexesAreValues (Exp.allocN (.val a) (.val b)) :=
  EctxItemLanguage.subredexes_are_values fun Ki e' h => by
    cases Ki <;> simp [fillItem, ECtxItem.fill] at h <;> first | rfl | (rcases h with ⟨rfl, -⟩; rfl) | (rcases h with ⟨-, rfl, -⟩; rfl) | (rcases h with ⟨-, -, rfl⟩; rfl) | (rcases h with ⟨-, rfl⟩; rfl)

theorem an_nb (v : Val) (σ : HeapLang.State) (obs e' σ' efs) :
    ¬ BaseStep (Exp.allocN (.val (.lit (.int 0))) (.val v)) σ obs e' σ' efs := by
  intro hs
  cases hs with
  | allocNS _ _ _ _ hn _ => exact absurd hn (by decide)

theorem d_get (l : Loc) : (default : HeapLang.State).get? l = none := rfl

def pid : ProphId := ⟨0⟩
/-- A state that is no erasure (erasure clears the used prophecy ids). -/
def σbad : HeapLang.State := ⟨∅, Std.ExtTreeSet.insert ∅ pid⟩
theorem es_ne (σ : HeapLang.State) : eraseState σ ≠ σbad := fun h => by
  have := congrArg (fun s : HeapLang.State => s.usedProphId.contains pid) h
  simp [eraseState, σbad] at this

theorem var_sr (x : String) : EctxLanguage.SubredexesAreValues (Exp.var x) :=
  EctxItemLanguage.subredexes_are_values fun Ki e' h => by cases Ki <;> simp [fillItem, ECtxItem.fill] at h

theorem var_nb (x : String) (σ obs e' σ' efs) : ¬ BaseStep (Exp.var x) σ obs e' σ' efs := fun h => by cases h

theorem var_irr (x : String) (σ : HeapLang.State) obs e' σ' efs :
    ¬ ((Exp.var x, σ) -<obs>-> (e', σ', efs)) := fun hs =>
  var_nb x _ _ _ _ _ (EctxLanguage.baseStep_of_primStep hs (var_sr x))

theorem var_ns (x : String) (σ : HeapLang.State) : ¬ PrimStep.NotStuck (Exp.var x, σ) := fun h => by
  rcases h with h | ⟨obs, e', σ', efs, hs⟩
  · exact Bool.noConfusion h
  · exact var_irr x σ obs e' σ' efs hs

theorem val_no_pure (v : Val) (e : Exp) : ¬ (Exp.val v -ᵖ-> e) := fun ⟨safe, _⟩ => by
  obtain ⟨e', σ', efs, hs⟩ := safe default
  exact absurd (Language.val_stuck hs) (by simp [ToVal.toVal])

theorem val_rtc {v : Val} {e : Exp} (h : Exp.val v -ᵖ->* e) : e = Exp.val v := by
  induction h with
  | refl => rfl
  | tail _ hs ih => subst ih; exact absurd hs (val_no_pure _ _)

theorem efst_ns : PrimStep.NotStuck (efst, (default : HeapLang.State)) :=
  .inr ⟨[], _, _, _, EctxLanguage.primStep_of_baseStep (.fstS i0 i0 default)⟩

theorem pid_used : σbad.usedProphId.contains pid = true := by simp [σbad]

abbrev eres : Exp := Exp.resolve efst (.val (.lit (.prophecy pid))) (.val i0)
theorem eres_ns : PrimStep.NotStuck (eres, σbad) :=
  .inr ⟨_, _, _, _, EctxLanguage.primStep_of_baseStep
    (.resolveS pid i0 efst σbad i0 σbad [] [] (.fstS i0 i0 σbad) pid_used)⟩

/-- `resolve(fst((#0,#0)), #0, w)`: the resolved value is no prophecy, so it is stuck. -/
theorem res0_sr (u w : Val) : EctxLanguage.SubredexesAreValues (Exp.resolve efst (.val u) (.val w)) :=
  EctxItemLanguage.subredexes_are_values fun Ki e' h => by
    cases Ki with
    | resolveL ctx _ _ =>
      cases ctx <;> simp [fillItem, ECtxItem.fill] at h
      obtain ⟨h1, -⟩ := h; subst h1; rfl
    | _ => simp [fillItem, ECtxItem.fill] at h <;> first | rfl | (rcases h with ⟨rfl, -⟩; rfl) | (rcases h with ⟨-, rfl, -⟩; rfl) | (rcases h with ⟨-, -, rfl⟩; rfl) | (rcases h with ⟨-, rfl⟩; rfl)

theorem res0_irr (w : Val) (σ : HeapLang.State) obs e' σ' efs :
    ¬ ((Exp.resolve efst (.val i0) (.val w), σ) -<obs>-> (e', σ', efs)) := fun hs => by
  have hb := EctxLanguage.baseStep_of_primStep hs (res0_sr i0 w)
  cases hb

/-- An expression without a pure step only reaches itself. -/
theorem rtc_stuck {e e2 : Exp} (hn : ∀ e', ¬ (e -ᵖ-> e')) (h : e -ᵖ->* e2) : e2 = e := by
  induction h with
  | refl => rfl
  | tail _ hs ih => subst ih; exact absurd hs (hn _)

theorem frames_np (a b : Val) (x : String) (e' : Exp) :
    ¬ (ProgramLogic.fill ([] ++ [ECtxItem.pairL a] ++ [ECtxItem.pairL b] ++ [ECtxItem.fst] ++ [ECtxItem.fst]) (Exp.var x) -ᵖ-> e') :=
  fun ⟨safe, _⟩ => by
    obtain ⟨e2, σ2, efs, hs⟩ := safe default
    obtain ⟨_, _, _, _, hs'⟩ := Language.Context.reducible_fill_inv
      (K := ProgramLogic.fill ([] ++ [ECtxItem.pairL a] ++ [ECtxItem.pairL b] ++ [ECtxItem.fst] ++ [ECtxItem.fst]))
      (e := Exp.var x) (σ := default) rfl ⟨[], e2, σ2, efs, hs⟩
    exact var_irr x _ _ _ _ _ hs'

theorem fst0_np (e' : Exp) : ¬ (Exp.fst (.val i0) -ᵖ-> e') := fun ⟨safe, _⟩ => by
  obtain ⟨e2, σ2, efs, hs⟩ := safe default
  have hsr : EctxLanguage.SubredexesAreValues (Exp.fst (.val i0)) :=
    EctxItemLanguage.subredexes_are_values fun Ki e' h => by
      cases Ki <;> simp [fillItem, ECtxItem.fill] at h; subst h; rfl
  have hb := EctxLanguage.baseStep_of_primStep hs hsr
  cases hb

end W6c3



namespace W6c3
open Iris Iris.BI Iris.HeapLang Iris.ProgramLogic Iris.ProgramLogic.Language.Notation

-- `Iris.ProofMode.subst_var_neq` idx 3: necessary (x = y = "x": substitution replaces the variable by the value)
theorem w6c3_1 : ¬ drop0% Iris.ProofMode.subst_var_neq 3 :=
  fun h => absurd (@h "x" "x" i0) (by simp [Exp.subst, Exp.substStr])

-- `Iris.ProofMode.subst_rec_eq` idx 5: necessary (x = "x", f = fx = anon, e = var x: substitution enters the body)
theorem w6c3_2 : ¬ drop0% Iris.ProofMode.subst_rec_eq 5 :=
  fun h => absurd (@h "x" .anon .anon (.var "x") i0) (by simp [Exp.subst, Exp.substStr])

-- `Iris.ProofMode.subst_rec_neq` idx 5: necessary (f = named x, fx = anon, e = var x: the binder shadows x, body unchanged)
theorem w6c3_3 : ¬ drop0% Iris.ProofMode.subst_rec_neq 5 :=
  fun h => absurd (@h "x" (.named "x") .anon (.var "x") i0 (by simp)) (by simp [Exp.subst, Exp.substStr])

-- `Iris.ProofMode.subst_rec_neq` idx 6: necessary (fx = named x, f = anon, e = var x: the binder shadows x, body unchanged)
theorem w6c3_4 : ¬ drop0% Iris.ProofMode.subst_rec_neq 6 :=
  fun h => absurd (@h "x" .anon (.named "x") (.var "x") i0 (by simp)) (by simp [Exp.subst, Exp.substStr])

-- `Iris.ProofMode.tac_wp_value` idx 8: necessary (HeapLang IProp (heap_adequacy, GF = HeapLangS), Δ = emp, v = #0, Φ = False: ⊢ WP #0 {{False}} contradicts adequacy)
theorem w6c3_5 : ¬ drop0% Iris.ProofMode.tac_wp_value 8 :=
  fun h => adeq_false _ default default i0 [] (fun _ => False) .refl id fun {_} =>
    @h .hasLC HS _ iprop(emp) .NotStuck ⊤ i0 (fun _ => iprop(⌜False⌝))

-- `Iris.ProofMode.tac_wp_value_nofupd` idx 8: necessary (as tac_wp_value: ⊢ WP #0 {{False}} contradicts heap_adequacy)
theorem w6c3_6 : ¬ drop0% Iris.ProofMode.tac_wp_value_nofupd 8 :=
  fun h => adeq_false _ default default i0 [] (fun _ => False) .refl id fun {_} =>
    @h .hasLC HS _ iprop(emp) .NotStuck ⊤ i0 (fun _ => iprop(⌜False⌝))

-- `Iris.ProofMode.tac_wp_expr_simp` idx 9: necessary (e = e' = #0, Φ = False, Δ = emp: ⊢ WP #0 {{False}} contradicts heap_adequacy)
theorem w6c3_7 : ¬ drop0% Iris.ProofMode.tac_wp_expr_simp 9 :=
  fun h => adeq_false _ default default i0 [] (fun _ => False) .refl id fun {_} =>
    @h .hasLC HS _ iprop(emp) .NotStuck ⊤ (ToVal.ofVal i0) (ToVal.ofVal i0) (fun _ => iprop(⌜False⌝)) rfl

-- `Iris.ProofMode.tac_wp_expr_simp` idx 10: necessary (e' = #1, e = #0, Φ v = ⌜v = #1⌝: WP #1 holds, WP #0 contradicts heap_adequacy)
theorem w6c3_8 : ¬ drop0% Iris.ProofMode.tac_wp_expr_simp 10 :=
  fun h => adeq_false _ default default i0 [] (fun w => w = i1) .refl i01 fun {_} =>
    @h .hasLC HS _ iprop(emp) .NotStuck ⊤ (ToVal.ofVal i0) (ToVal.ofVal i1) (fun w => iprop(⌜w = i1⌝)) (vpost _ i1)

-- `Iris.ProofMode.tac_wp_bind` idx 9: necessary (K = [], e' = #0, Φ = False: ⊢ WP #0 {{False}} contradicts heap_adequacy)
theorem w6c3_9 : ¬ drop0% Iris.ProofMode.tac_wp_bind 9 :=
  fun h => adeq_false _ default default i0 [] (fun _ => False) .refl id fun {_} =>
    @h .hasLC HS _ iprop(emp) .NotStuck ⊤ [] (ToVal.ofVal i0) (fun _ => iprop(⌜False⌝))

-- `Iris.ProofMode.tac_wp_pure` idx 13: necessary (φ = True, n = 0, e₁ = #0, e₂ = #1, Φ v = ⌜v = #1⌝: WP #0 {{v = #1}} contradicts heap_adequacy)
theorem w6c3_10 : ¬ drop0% Iris.ProofMode.tac_wp_pure 13 :=
  fun h => adeq_false _ default default i0 [] (fun w => w = i1) .refl i01 fun {_} =>
    @h .hasLC HS _ iprop(emp) iprop(emp) .NotStuck ⊤ [] (ToVal.ofVal i0) (ToVal.ofVal i1) True 0
      (fun w => iprop(⌜w = i1⌝)) trivial .rfl (vpost _ i1)

-- `Iris.ProofMode.tac_wp_pure` idx 15: necessary (n = 0, e₁ = e₂ = #0, Δ = emp, Δ' = False, Φ = False: ⊢ WP #0 {{False}} contradicts heap_adequacy)
theorem w6c3_11 : ¬ drop0% Iris.ProofMode.tac_wp_pure 15 :=
  fun h => adeq_false _ default default i0 [] (fun _ => False) .refl id fun {_} =>
    @h .hasLC HS _ iprop(emp) iprop(False) .NotStuck ⊤ [] (ToVal.ofVal i0) (ToVal.ofVal i0) True 0
      (fun _ => iprop(⌜False⌝)) (pe0 _) trivial false_elim

-- `Iris.ProofMode.tac_wp_pure` idx 16: necessary (n = 0, e₁ = e₂ = #0, Δ = Δ' = emp, Φ = False: ⊢ WP #0 {{False}} contradicts heap_adequacy)
theorem w6c3_12 : ¬ drop0% Iris.ProofMode.tac_wp_pure 16 :=
  fun h => adeq_false _ default default i0 [] (fun _ => False) .refl id fun {_} =>
    @h .hasLC HS _ iprop(emp) iprop(emp) .NotStuck ⊤ [] (ToVal.ofVal i0) (ToVal.ofVal i0) True 0
      (fun _ => iprop(⌜False⌝)) (pe0 _) trivial .rfl

-- `_private.Iris.HeapLang.ProofMode.0.Iris.ProofMode.lookup_split` idx 5: necessary (non-affine BI GB (Bool → Prop, sep over xor), P = True, p = true, Δ'' = emp: □True ⊬ True ∗ (True -∗ □True) at world false)
theorem w6c3_13 : ¬ drop0% _private.Iris.HeapLang.ProofMode.«0».Iris.ProofMode.lookup_split 5 :=
  fun h => by
  obtain ⟨a, b, _, _, hw⟩ := @h GB gbBI iprop(□ True) iprop(emp) iprop(True) true emp_sep.symm false ⟨rfl, trivial⟩
  have := (hw (!b) trivial).1
  cases b <;> exact Bool.noConfusion this

-- `_private.Iris.HeapLang.ProofMode.0.Iris.ProofMode.lookup_split` idx 7: necessary (SiProp, Δ' = Δ'' = True, P = False: True ⊬ False ∗ _)
theorem w6c3_14 : ¬ drop0% _private.Iris.HeapLang.ProofMode.«0».Iris.ProofMode.lookup_split 7 :=
  fun h => ((@h SiProp _ iprop(True) iprop(True) iprop(False) _ false) 0 trivial).1

-- `_private.Iris.HeapLang.ProofMode.0.Iris.ProofMode.wp_exact_of_triple` idx 9: necessary (e = #0, r = #1, P = P' = emp: ▷emp ⊢ WP #0 {{v = #1 ∗ emp}} contradicts heap_adequacy)
theorem w6c3_15 : ¬ drop0% _private.Iris.HeapLang.ProofMode.«0».Iris.ProofMode.wp_exact_of_triple 9 :=
  fun h => adeq_false _ default default i0 [] (fun w => w = i1) .refl i01 fun {_} =>
    later_intro.trans ((@h .hasLC HS _ .NotStuck ⊤ (ToVal.ofVal i0) i1 iprop(emp) iprop(emp)).trans (wp_mono fun _ => sep_elim_left))

-- `_private.Iris.HeapLang.ProofMode.0.Iris.ProofMode.tac_wp_heap_op` idx 15: necessary (e = fst((#0,#0)) (steps to #0), r = #1, all contexts emp, Φ v = ⌜v = #1⌝: contradicts heap_adequacy)
theorem w6c3_16 : ¬ drop0% _private.Iris.HeapLang.ProofMode.«0».Iris.ProofMode.tac_wp_heap_op 15 :=
  fun h => adeq_false _ default default i0 [] (fun w => w = i1) fstep i01 fun {_} =>
    @h .hasLC HS _ iprop(emp) iprop(emp) iprop(emp) iprop(emp) iprop(emp) .NotStuck ⊤ [] efst i1 (fun w => iprop(⌜w = i1⌝))
      rfl later_intro emp_sep.symm (vpost _ i1)

-- `_private.Iris.HeapLang.ProofMode.0.Iris.ProofMode.tac_wp_heap_op` idx 16: necessary (e = fst((#0,#0)), Δ = emp, Δ' = Δ'' = False, Φ = False: WP e {{False}} contradicts heap_adequacy)
theorem w6c3_17 : ¬ drop0% _private.Iris.HeapLang.ProofMode.«0».Iris.ProofMode.tac_wp_heap_op 16 :=
  fun h => adeq_false _ default default i0 [] (fun _ => False) fstep id fun {_} =>
    @h .hasLC HS _ iprop(emp) iprop(False) iprop(False) iprop(emp) iprop(emp) .NotStuck ⊤ [] efst i0 (fun _ => iprop(⌜False⌝))
      rfl hwp_fst ⟨false_elim, sep_elim_left⟩ (sep_elim_left.trans false_elim)

-- `_private.Iris.HeapLang.ProofMode.0.Iris.ProofMode.tac_wp_heap_op` idx 17: necessary (e = fst((#0,#0)), Δ = Δ' = emp, Δ'' = False, Φ = False: WP e {{False}} contradicts heap_adequacy)
theorem w6c3_18 : ¬ drop0% _private.Iris.HeapLang.ProofMode.«0».Iris.ProofMode.tac_wp_heap_op 17 :=
  fun h => adeq_false _ default default i0 [] (fun _ => False) fstep id fun {_} =>
    @h .hasLC HS _ iprop(emp) iprop(emp) iprop(False) iprop(emp) iprop(emp) .NotStuck ⊤ [] efst i0 (fun _ => iprop(⌜False⌝))
      rfl hwp_fst later_intro (sep_elim_left.trans false_elim)

-- `_private.Iris.HeapLang.ProofMode.0.Iris.ProofMode.tac_wp_heap_op` idx 18: necessary (e = fst((#0,#0)), all contexts emp, Φ = False: WP e {{False}} contradicts heap_adequacy)
theorem w6c3_19 : ¬ drop0% _private.Iris.HeapLang.ProofMode.«0».Iris.ProofMode.tac_wp_heap_op 18 :=
  fun h => adeq_false _ default default i0 [] (fun _ => False) fstep id fun {_} =>
    @h .hasLC HS _ iprop(emp) iprop(emp) iprop(emp) iprop(emp) iprop(emp) .NotStuck ⊤ [] efst i0 (fun _ => iprop(⌜False⌝))
      rfl hwp_fst later_intro emp_sep.symm

-- `Iris.ProofMode.tac_wp_alloc` idx 10: necessary (Δ = emp, Δ' = False, Φ = False: ⊢ WP ref #0 {{False}}; ref #0 steps to a value, contradicting heap_adequacy)
theorem w6c3_20 : ¬ drop0% Iris.ProofMode.tac_wp_alloc 10 :=
  fun h => adeq_false _ default _ _ [] (fun _ => False) (astep i0) id fun {_} =>
    @h .hasLC HS _ iprop(emp) iprop(False) .NotStuck ⊤ [] i0 (fun _ => iprop(⌜False⌝)) fun _ => (sep_elim_left.trans false_elim)

-- `Iris.ProofMode.tac_wp_alloc` idx 11: necessary (Δ = Δ' = emp, Φ = False: ⊢ WP ref #0 {{False}} contradicts heap_adequacy)
theorem w6c3_21 : ¬ drop0% Iris.ProofMode.tac_wp_alloc 11 :=
  fun h => adeq_false _ default _ _ [] (fun _ => False) (astep i0) id fun {_} =>
    @h .hasLC HS _ iprop(emp) iprop(emp) .NotStuck ⊤ [] i0 (fun _ => iprop(⌜False⌝)) later_intro

-- `Iris.ProofMode.tac_wp_free` idx 12: necessary (Δ = emp, Δ' = Δ'' = False, Φ = False: WP free #l {{False}}, free steps in a heap with l allocated: contradicts heap_adequacy)
theorem w6c3_22 : ¬ drop0% Iris.ProofMode.tac_wp_free 12 :=
  fun h => adeq_false _ (σ1 i0) _ (.lit .unit) [] (fun _ => False) (bstep (.freeS l0 i0 _ (σ1_get i0))) id fun {_} =>
    @h .hasLC HS _ iprop(emp) iprop(False) iprop(False) .NotStuck ⊤ [] l0 i0 (fun _ => iprop(⌜False⌝)) ⟨false_elim, sep_elim_left⟩ false_elim

-- `Iris.ProofMode.tac_wp_free` idx 13: necessary (Δ = Δ' = emp, Δ'' = False, Φ = False: WP free #l {{False}} contradicts heap_adequacy)
theorem w6c3_23 : ¬ drop0% Iris.ProofMode.tac_wp_free 13 :=
  fun h => adeq_false _ (σ1 i0) _ (.lit .unit) [] (fun _ => False) (bstep (.freeS l0 i0 _ (σ1_get i0))) id fun {_} =>
    @h .hasLC HS _ iprop(emp) iprop(emp) iprop(False) .NotStuck ⊤ [] l0 i0 (fun _ => iprop(⌜False⌝)) later_intro false_elim

-- `Iris.ProofMode.tac_wp_free` idx 14: necessary (Δ = Δ' = l ↦ #0, Δ'' = emp, Φ = False: l ↦ #0 ⊢ WP free #l {{False}}; with wp_alloc, ⊢ WP free (ref #0) {{False}} contradicts heap_adequacy)
theorem w6c3_24 : ¬ drop0% Iris.ProofMode.tac_wp_free 14 :=
  fun h => adeq_alloc .free i0 (fun _ => False) _ (.lit .unit) [] (bstep (.freeS l0 i0 _ (σ1_get i0))) id fun {_} l =>
    @h .hasLC HS _ iprop(l ↦ some i0) iprop(l ↦ some i0) iprop(emp) .NotStuck ⊤ [] l i0 (fun _ => iprop(⌜False⌝))
      later_intro emp_sep.symm

-- `Iris.ProofMode.tac_wp_load` idx 14: necessary (Δ = emp, Δ' = Δ'' = False, Φ = False: WP !#l {{False}} contradicts heap_adequacy)
theorem w6c3_25 : ¬ drop0% Iris.ProofMode.tac_wp_load 14 :=
  fun h => adeq_false _ (σ1 i0) _ i0 [] (fun _ => False) (bstep (.loadS l0 i0 _ (σ1_get i0))) id fun {_} =>
    @h .hasLC HS _ iprop(emp) iprop(False) iprop(False) false .NotStuck ⊤ [] l0 (DFrac.own 1) i0 (fun _ => iprop(⌜False⌝)) ⟨false_elim, sep_elim_left⟩ false_elim

-- `Iris.ProofMode.tac_wp_load` idx 15: necessary (Δ = Δ' = emp, v = #1, Φ w = ⌜w = #1⌝: WP !#l {{w = #1}}, but l holds #0: contradicts heap_adequacy)
theorem w6c3_26 : ¬ drop0% Iris.ProofMode.tac_wp_load 15 :=
  fun h => adeq_false _ (σ1 i0) _ i0 [] (fun w => w = i1) (bstep (.loadS l0 i0 _ (σ1_get i0))) i01 fun {_} =>
    @h .hasLC HS _ iprop(emp) iprop(emp) iprop(emp) false .NotStuck ⊤ [] l0 (DFrac.own 1) i1 (fun w => iprop(⌜w = i1⌝))
      later_intro (vpost _ i1)

-- `Iris.ProofMode.tac_wp_load` idx 16: necessary (Δ = Δ' = l ↦ #0, Δ'' = emp, Φ = False: via wp_alloc, ⊢ WP !(ref #0) {{False}} contradicts heap_adequacy)
theorem w6c3_27 : ¬ drop0% Iris.ProofMode.tac_wp_load 16 :=
  fun h => adeq_alloc .load i0 (fun _ => False) _ i0 [] (bstep (.loadS l0 i0 _ (σ1_get i0))) id fun {_} l =>
    @h .hasLC HS _ iprop(l ↦ some i0) iprop(l ↦ some i0) iprop(emp) false .NotStuck ⊤ [] l (DFrac.own 1) i0 (fun _ => iprop(⌜False⌝))
      later_intro emp_sep.symm

-- `Iris.ProofMode.tac_wp_store` idx 13: necessary (Δ = emp, Δ' = Δ'' = False, Φ = False: WP #l ← #1 {{False}} contradicts heap_adequacy)
theorem w6c3_28 : ¬ drop0% Iris.ProofMode.tac_wp_store 13 :=
  fun h => adeq_false _ (σ1 i0) _ (.lit .unit) [] (fun _ => False) (bstep (.storeS l0 i0 i1 _ (σ1_get i0))) id fun {_} =>
    @h .hasLC HS _ iprop(emp) iprop(False) iprop(False) .NotStuck ⊤ [] l0 i0 i1 (fun _ => iprop(⌜False⌝)) ⟨false_elim, sep_elim_left⟩ (sep_elim_left.trans false_elim)

-- `Iris.ProofMode.tac_wp_store` idx 14: necessary (Δ = Δ' = emp, Δ'' = False, Φ = False: WP #l ← #1 {{False}} contradicts heap_adequacy)
theorem w6c3_29 : ¬ drop0% Iris.ProofMode.tac_wp_store 14 :=
  fun h => adeq_false _ (σ1 i0) _ (.lit .unit) [] (fun _ => False) (bstep (.storeS l0 i0 i1 _ (σ1_get i0))) id fun {_} =>
    @h .hasLC HS _ iprop(emp) iprop(emp) iprop(False) .NotStuck ⊤ [] l0 i0 i1 (fun _ => iprop(⌜False⌝)) later_intro (sep_elim_left.trans false_elim)

-- `Iris.ProofMode.tac_wp_store` idx 15: necessary (Δ = Δ' = l ↦ #0, Δ'' = emp, Φ = False: via wp_alloc, ⊢ WP (ref #0) ← #1 {{False}} contradicts heap_adequacy)
theorem w6c3_30 : ¬ drop0% Iris.ProofMode.tac_wp_store 15 :=
  fun h => adeq_alloc (.storeL i1) i0 (fun _ => False) _ (.lit .unit) [] (bstep (.storeS l0 i0 i1 _ (σ1_get i0))) id fun {_} l =>
    @h .hasLC HS _ iprop(l ↦ some i0) iprop(l ↦ some i0) iprop(emp) .NotStuck ⊤ [] l i0 i1 (fun _ => iprop(⌜False⌝))
      later_intro emp_sep.symm

-- `Iris.ProofMode.tac_wp_xchg` idx 13: necessary (Δ = emp, Δ' = Δ'' = False, Φ = False: WP xchg(#l, #1) {{False}} contradicts heap_adequacy)
theorem w6c3_31 : ¬ drop0% Iris.ProofMode.tac_wp_xchg 13 :=
  fun h => adeq_false _ (σ1 i0) _ i0 [] (fun _ => False) (bstep (.xchgS l0 i0 i1 _ (σ1_get i0))) id fun {_} =>
    @h .hasLC HS _ iprop(emp) iprop(False) iprop(False) .NotStuck ⊤ [] l0 i0 i1 (fun _ => iprop(⌜False⌝)) ⟨false_elim, sep_elim_left⟩ (sep_elim_left.trans false_elim)

-- `Iris.ProofMode.tac_wp_xchg` idx 14: necessary (Δ = Δ' = emp, Δ'' = False, Φ = False: WP xchg(#l, #1) {{False}} contradicts heap_adequacy)
theorem w6c3_32 : ¬ drop0% Iris.ProofMode.tac_wp_xchg 14 :=
  fun h => adeq_false _ (σ1 i0) _ i0 [] (fun _ => False) (bstep (.xchgS l0 i0 i1 _ (σ1_get i0))) id fun {_} =>
    @h .hasLC HS _ iprop(emp) iprop(emp) iprop(False) .NotStuck ⊤ [] l0 i0 i1 (fun _ => iprop(⌜False⌝)) later_intro (sep_elim_left.trans false_elim)

-- `Iris.ProofMode.tac_wp_xchg` idx 15: necessary (Δ = Δ' = l ↦ #0, Δ'' = emp, Φ = False: via wp_alloc, ⊢ WP xchg(ref #0, #1) {{False}} contradicts heap_adequacy)
theorem w6c3_33 : ¬ drop0% Iris.ProofMode.tac_wp_xchg 15 :=
  fun h => adeq_alloc (.xchgL i1) i0 (fun _ => False) _ i0 [] (bstep (.xchgS l0 i0 i1 _ (σ1_get i0))) id fun {_} l =>
    @h .hasLC HS _ iprop(l ↦ some i0) iprop(l ↦ some i0) iprop(emp) .NotStuck ⊤ [] l i0 i1 (fun _ => iprop(⌜False⌝))
      later_intro emp_sep.symm

-- `Iris.ProofMode.tac_wp_cmpXchg_fail` idx 16: necessary (Δ = emp, Δ' = Δ'' = False, l ↦ #0, v1 = #1, Φ = False: WP cmpXchg {{False}} contradicts heap_adequacy)
theorem w6c3_34 : ¬ drop0% Iris.ProofMode.tac_wp_cmpXchg_fail 16 :=
  fun h => adeq_false _ (σ1 i0) _ (ipair i0 false) [] (fun _ => False) (bstep (.cmpXchgS l0 i1 i0 i0 _ false (σ1_get i0) rfl (by decide))) id fun {_} =>
    @h .hasLC HS _ iprop(emp) iprop(False) iprop(False) false .NotStuck ⊤ [] l0 (DFrac.own 1) i0 i1 i0 (fun _ => iprop(⌜False⌝)) ⟨false_elim, sep_elim_left⟩ i01 rfl false_elim

-- `Iris.ProofMode.tac_wp_cmpXchg_fail` idx 17: necessary (Δ = Δ' = emp, v = #0, v1 = #1, Φ w = ⌜w = (#0, false)⌝; heap l ↦ #1: the CAS succeeds with (#1, true), contradicting heap_adequacy)
theorem w6c3_35 : ¬ drop0% Iris.ProofMode.tac_wp_cmpXchg_fail 17 :=
  fun h => adeq_false _ (σ1 i1) _ (ipair i1 true) [] (fun w => w = ipair i0 false)
    (bstep (.cmpXchgS l0 i1 i0 i1 _ true (σ1_get i1) rfl (by decide))) (by decide) fun {_} =>
    @h .hasLC HS _ iprop(emp) iprop(emp) iprop(emp) false .NotStuck ⊤ [] l0 (DFrac.own 1) i0 i1 i0
      (fun w => iprop(⌜w = ipair i0 false⌝)) later_intro i01 rfl (vpost _ (ipair i0 false))

-- `Iris.ProofMode.tac_wp_cmpXchg_fail` idx 18: necessary (v = v1 = #0, Δ = Δ' = l ↦ #0, Φ w = ⌜w = (#0, false)⌝: via wp_alloc, the CAS succeeds with (#0, true), contradicting heap_adequacy)
theorem w6c3_36 : ¬ drop0% Iris.ProofMode.tac_wp_cmpXchg_fail 18 :=
  fun h => adeq_alloc (.cmpXchgL i0 i1) i0 (fun w => w = ipair i0 false) _ (ipair i0 true) []
    (bstep (.cmpXchgS l0 i0 i1 i0 _ true (σ1_get i0) rfl (by decide))) (by decide) fun {_} l =>
    @h .hasLC HS _ iprop(l ↦ some i0) iprop(l ↦ some i0) iprop(emp) false .NotStuck ⊤ [] l (DFrac.own 1) i0 i0 i1
      (fun w => iprop(⌜w = ipair i0 false⌝)) later_intro emp_sep.symm rfl (vpost _ (ipair i0 false))

-- `Iris.ProofMode.tac_wp_cmpXchg_fail` idx 20: necessary (Δ = Δ' = l ↦ #0, Δ'' = emp, v1 = #1, Φ = False: via wp_alloc, ⊢ WP cmpXchg(ref #0, #1, #0) {{False}} contradicts heap_adequacy)
theorem w6c3_37 : ¬ drop0% Iris.ProofMode.tac_wp_cmpXchg_fail 20 :=
  fun h => adeq_alloc (.cmpXchgL i1 i0) i0 (fun _ => False) _ (ipair i0 false) [] (bstep (.cmpXchgS l0 i1 i0 i0 _ false (σ1_get i0) rfl (by decide))) id fun {_} l =>
    @h .hasLC HS _ iprop(l ↦ some i0) iprop(l ↦ some i0) iprop(emp) false .NotStuck ⊤ [] l (DFrac.own 1) i0 i1 i0 (fun _ => iprop(⌜False⌝))
      later_intro emp_sep.symm i01 rfl

-- `Iris.ProofMode.tac_wp_cmpXchg_suc` idx 14: necessary (Δ = emp, Δ' = Δ'' = False, v = v1 = #0, Φ = False: WP cmpXchg {{False}} contradicts heap_adequacy)
theorem w6c3_38 : ¬ drop0% Iris.ProofMode.tac_wp_cmpXchg_suc 14 :=
  fun h => adeq_false _ (σ1 i0) _ (ipair i0 true) [] (fun _ => False) (bstep (.cmpXchgS l0 i0 i1 i0 _ true (σ1_get i0) rfl (by decide))) id fun {_} =>
    @h .hasLC HS _ iprop(emp) iprop(False) iprop(False) .NotStuck ⊤ [] l0 i0 i0 i1 (fun _ => iprop(⌜False⌝)) ⟨false_elim, sep_elim_left⟩ rfl rfl (sep_elim_left.trans false_elim)

-- `Iris.ProofMode.tac_wp_cmpXchg_suc` idx 15: necessary (Δ = Δ' = emp, Δ'' = False, v = v1 = #0, Φ = False: WP cmpXchg {{False}} contradicts heap_adequacy)
theorem w6c3_39 : ¬ drop0% Iris.ProofMode.tac_wp_cmpXchg_suc 15 :=
  fun h => adeq_false _ (σ1 i0) _ (ipair i0 true) [] (fun _ => False) (bstep (.cmpXchgS l0 i0 i1 i0 _ true (σ1_get i0) rfl (by decide))) id fun {_} =>
    @h .hasLC HS _ iprop(emp) iprop(emp) iprop(False) .NotStuck ⊤ [] l0 i0 i0 i1 (fun _ => iprop(⌜False⌝)) later_intro rfl rfl (sep_elim_left.trans false_elim)

-- `Iris.ProofMode.tac_wp_cmpXchg_suc` idx 16: necessary (v = #0, v1 = #1, Δ = Δ' = l ↦ #0, Φ w = ⌜w = (#0, true)⌝: via wp_alloc, the CAS fails with (#0, false), contradicting heap_adequacy)
theorem w6c3_40 : ¬ drop0% Iris.ProofMode.tac_wp_cmpXchg_suc 16 :=
  fun h => adeq_alloc (.cmpXchgL i1 i0) i0 (fun w => w = ipair i0 true) _ (ipair i0 false) []
    (bstep (.cmpXchgS l0 i1 i0 i0 _ false (σ1_get i0) rfl (by decide))) (by decide) fun {_} l =>
    @h .hasLC HS _ iprop(l ↦ some i0) iprop(l ↦ some i0) iprop(emp) .NotStuck ⊤ [] l i0 i1 i0
      (fun w => iprop(⌜w = ipair i0 true⌝)) later_intro emp_sep.symm rfl (vpost _ (ipair i0 true))

-- `Iris.ProofMode.tac_wp_cmpXchg_suc` idx 18: necessary (Δ = Δ' = l ↦ #0, Δ'' = emp, v = v1 = #0, Φ = False: via wp_alloc, contradicts heap_adequacy)
theorem w6c3_41 : ¬ drop0% Iris.ProofMode.tac_wp_cmpXchg_suc 18 :=
  fun h => adeq_alloc (.cmpXchgL i0 i1) i0 (fun _ => False) _ (ipair i0 true) [] (bstep (.cmpXchgS l0 i0 i1 i0 _ true (σ1_get i0) rfl (by decide))) id fun {_} l =>
    @h .hasLC HS _ iprop(l ↦ some i0) iprop(l ↦ some i0) iprop(emp) .NotStuck ⊤ [] l i0 i0 i1 (fun _ => iprop(⌜False⌝))
      later_intro emp_sep.symm rfl rfl

-- `Iris.ProofMode.tac_wp_cmpXchg` idx 14: necessary (Δ = emp, Δ' = Δ'' = False, v = v1 = #0, Φ = False: WP cmpXchg {{False}} contradicts heap_adequacy)
theorem w6c3_42 : ¬ drop0% Iris.ProofMode.tac_wp_cmpXchg 14 :=
  fun h => adeq_false _ (σ1 i0) _ (ipair i0 true) [] (fun _ => False) (bstep (.cmpXchgS l0 i0 i1 i0 _ true (σ1_get i0) rfl (by decide))) id fun {_} =>
    @h .hasLC HS _ iprop(emp) iprop(False) iprop(False) .NotStuck ⊤ [] l0 i0 i0 i1 (fun _ => iprop(⌜False⌝)) ⟨false_elim, sep_elim_left⟩ rfl (fun _ => (sep_elim_left.trans false_elim)) (fun _ => false_elim)

-- `Iris.ProofMode.tac_wp_cmpXchg` idx 15: necessary (Δ = Δ' = emp, Δ'' = False, v = v1 = #0 (hfail vacuous), Φ = False: WP cmpXchg {{False}} contradicts heap_adequacy)
theorem w6c3_43 : ¬ drop0% Iris.ProofMode.tac_wp_cmpXchg 15 :=
  fun h => adeq_false _ (σ1 i0) _ (ipair i0 true) [] (fun _ => False) (bstep (.cmpXchgS l0 i0 i1 i0 _ true (σ1_get i0) rfl (by decide))) id fun {_} =>
    @h .hasLC HS _ iprop(emp) iprop(emp) iprop(False) .NotStuck ⊤ [] l0 i0 i0 i1 (fun _ => iprop(⌜False⌝)) later_intro rfl (fun _ => (sep_elim_left.trans false_elim)) (fun hne => absurd rfl hne)

-- `Iris.ProofMode.tac_wp_cmpXchg` idx 17: necessary (Δ = Δ' = l ↦ #0, v = v1 = #0 (hfail vacuous), Φ = False: via wp_alloc, contradicts heap_adequacy)
theorem w6c3_44 : ¬ drop0% Iris.ProofMode.tac_wp_cmpXchg 17 :=
  fun h => adeq_alloc (.cmpXchgL i0 i1) i0 (fun _ => False) _ (ipair i0 true) [] (bstep (.cmpXchgS l0 i0 i1 i0 _ true (σ1_get i0) rfl (by decide))) id fun {_} l =>
    @h .hasLC HS _ iprop(l ↦ some i0) iprop(l ↦ some i0) iprop(emp) .NotStuck ⊤ [] l i0 i0 i1 (fun _ => iprop(⌜False⌝))
      later_intro emp_sep.symm rfl (fun hne => absurd rfl hne)

-- `Iris.ProofMode.tac_wp_cmpXchg` idx 18: necessary (Δ = Δ' = l ↦ #0, v = #0, v1 = #1 (hsuc vacuous), Φ = False: via wp_alloc, contradicts heap_adequacy)
theorem w6c3_45 : ¬ drop0% Iris.ProofMode.tac_wp_cmpXchg 18 :=
  fun h => adeq_alloc (.cmpXchgL i1 i0) i0 (fun _ => False) _ (ipair i0 false) [] (bstep (.cmpXchgS l0 i1 i0 i0 _ false (σ1_get i0) rfl (by decide))) id fun {_} l =>
    @h .hasLC HS _ iprop(l ↦ some i0) iprop(l ↦ some i0) iprop(emp) .NotStuck ⊤ [] l i0 i1 i0 (fun _ => iprop(⌜False⌝))
      later_intro emp_sep.symm rfl (fun heq => absurd heq i01)

-- `Iris.ProofMode.tac_wp_faa` idx 13: necessary (Δ = emp, Δ' = Δ'' = False, Φ = False: WP faa(#l, #0) {{False}} contradicts heap_adequacy)
theorem w6c3_46 : ¬ drop0% Iris.ProofMode.tac_wp_faa 13 :=
  fun h => adeq_false _ (σ1 i0) _ i0 [] (fun _ => False) (bstep (.faaS l0 0 0 _ (σ1_get i0))) id fun {_} =>
    @h .hasLC HS _ iprop(emp) iprop(False) iprop(False) .NotStuck ⊤ [] l0 0 0 (fun _ => iprop(⌜False⌝)) ⟨false_elim, sep_elim_left⟩ (sep_elim_left.trans false_elim)

-- `Iris.ProofMode.tac_wp_faa` idx 14: necessary (Δ = Δ' = emp, Δ'' = False, Φ = False: WP faa(#l, #0) {{False}} contradicts heap_adequacy)
theorem w6c3_47 : ¬ drop0% Iris.ProofMode.tac_wp_faa 14 :=
  fun h => adeq_false _ (σ1 i0) _ i0 [] (fun _ => False) (bstep (.faaS l0 0 0 _ (σ1_get i0))) id fun {_} =>
    @h .hasLC HS _ iprop(emp) iprop(emp) iprop(False) .NotStuck ⊤ [] l0 0 0 (fun _ => iprop(⌜False⌝)) later_intro (sep_elim_left.trans false_elim)

-- `Iris.ProofMode.tac_wp_faa` idx 15: necessary (Δ = Δ' = l ↦ #0, Δ'' = emp, Φ = False: via wp_alloc, contradicts heap_adequacy)
theorem w6c3_48 : ¬ drop0% Iris.ProofMode.tac_wp_faa 15 :=
  fun h => adeq_alloc (.faaL i0) i0 (fun _ => False) _ i0 [] (bstep (.faaS l0 0 0 _ (σ1_get i0))) id fun {_} l =>
    @h .hasLC HS _ iprop(l ↦ some i0) iprop(l ↦ some i0) iprop(emp) .NotStuck ⊤ [] l 0 0 (fun _ => iprop(⌜False⌝))
      later_intro emp_sep.symm

-- `Iris.ProofMode.tac_wp_allocN` idx 12: necessary (n = 1, Δ = emp, Δ' = False, Φ = False: ⊢ WP allocN(#1, #0) {{False}} contradicts heap_adequacy)
theorem w6c3_49 : ¬ drop0% Iris.ProofMode.tac_wp_allocN 12 :=
  fun h => adeq_false _ default _ _ [] (fun _ => False) (astep i0) id fun {_} =>
    @h .hasLC HS _ iprop(emp) iprop(False) .NotStuck ⊤ [] i0 1 (fun _ => iprop(⌜False⌝)) (by decide) fun _ => (sep_elim_left.trans false_elim)

-- `Iris.ProofMode.tac_wp_allocN` idx 13: necessary (n = 1, Δ = Δ' = emp, Φ = False: ⊢ WP allocN(#1, #0) {{False}} contradicts heap_adequacy)
theorem w6c3_50 : ¬ drop0% Iris.ProofMode.tac_wp_allocN 13 :=
  fun h => adeq_false _ default _ _ [] (fun _ => False) (astep i0) id fun {_} =>
    @h .hasLC HS _ iprop(emp) iprop(emp) .NotStuck ⊤ [] i0 1 (fun _ => iprop(⌜False⌝)) (by decide) later_intro

-- `Iris.ProofMode.tac_wp_allocN` idx 11: necessary (n = 0, Δ = Δ' = emp, Φ = True: ⊢ WP allocN(#0, #0) {{True}}, but allocN(#0, _) is stuck (allocNS needs 0 < n): contradicts the not-stuck part of heap_adequacy)
theorem w6c3_51 : ¬ drop0% Iris.ProofMode.tac_wp_allocN 11 :=
  fun h => stuck_adeq _ _ default default (fun _ => True) .refl rfl (an_sr _ _) (an_nb i0 default) fun {_} =>
    @h .hasLC HS _ iprop(emp) iprop(emp) .NotStuck ⊤ [] i0 0 (fun _ => iprop(⌜True⌝)) later_intro (fun l => ((pure_intro trivial).trans (wp_value' (Φ := fun _ => iprop(⌜True⌝)) (v := (Val.lit (.loc l))))))

-- `Iris.ProofMode.tac_wp_cmpXchg_fail` idx 19: necessary (v = (#0,#0), v1 = (#1,#1) (not compare-safe), Δ = Δ' = l ↦ v, Φ = True: via wp_alloc, cmpXchg(#l, v1, _) is stuck after the allocation: contradicts heap_adequacy (not stuck))
theorem w6c3_52 : ¬ drop0% Iris.ProofMode.tac_wp_cmpXchg_fail 19 :=
  fun h => stuck_adeq _ _ default (σ1 vp) (fun _ => True) (.single (alloc_step (.cmpXchgL vq i0) vp)) rfl (cx_sr _ _ _) (cx_nb vq i0 rfl)
    fun {_} => alloc_then (.cmpXchgL vq i0) vp (fun _ => True) fun l =>
    @h .hasLC HS _ iprop(l ↦ some vp) iprop(l ↦ some vp) iprop(emp) false .NotStuck ⊤ [] l (DFrac.own 1) vp vq i0 (fun _ => iprop(⌜True⌝))
      later_intro emp_sep.symm (by decide) ((pure_intro trivial).trans (wp_value' (Φ := fun _ => iprop(⌜True⌝)) (v := (ipair vp false))))

-- `Iris.ProofMode.tac_wp_cmpXchg_suc` idx 17: necessary (v = v1 = (#0,#0) (not compare-safe), Δ = Δ' = l ↦ v, Φ = True: via wp_alloc, the CAS is stuck: contradicts heap_adequacy (not stuck))
theorem w6c3_53 : ¬ drop0% Iris.ProofMode.tac_wp_cmpXchg_suc 17 :=
  fun h => stuck_adeq _ _ default (σ1 vp) (fun _ => True) (.single (alloc_step (.cmpXchgL vp i0) vp)) rfl (cx_sr _ _ _) (cx_nb vp i0 rfl)
    fun {_} => alloc_then (.cmpXchgL vp i0) vp (fun _ => True) fun l =>
    @h .hasLC HS _ iprop(l ↦ some vp) iprop(l ↦ some vp) iprop(emp) .NotStuck ⊤ [] l vp vp i0 (fun _ => iprop(⌜True⌝))
      later_intro emp_sep.symm rfl ((pure_intro trivial).trans (wp_value' (Φ := fun _ => iprop(⌜True⌝)) (v := (ipair vp true))))

-- `Iris.ProofMode.tac_wp_cmpXchg` idx 16: necessary (v = v1 = (#0,#0) (not compare-safe), Δ = Δ' = l ↦ v, Φ = True: via wp_alloc, the CAS is stuck: contradicts heap_adequacy (not stuck))
theorem w6c3_54 : ¬ drop0% Iris.ProofMode.tac_wp_cmpXchg 16 :=
  fun h => stuck_adeq _ _ default (σ1 vp) (fun _ => True) (.single (alloc_step (.cmpXchgL vp i0) vp)) rfl (cx_sr _ _ _) (cx_nb vp i0 rfl)
    fun {_} => alloc_then (.cmpXchgL vp i0) vp (fun _ => True) fun l =>
    @h .hasLC HS _ iprop(l ↦ some vp) iprop(l ↦ some vp) iprop(emp) .NotStuck ⊤ [] l vp vp i0 (fun _ => iprop(⌜True⌝))
      later_intro emp_sep.symm (fun _ => ((pure_intro trivial).trans (wp_value' (Φ := fun _ => iprop(⌜True⌝)) (v := (ipair vp true))))) (fun _ => ((pure_intro trivial).trans (wp_value' (Φ := fun _ => iprop(⌜True⌝)) (v := (ipair vp false)))))

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.eraseExpr_eq_val` idx 2: necessary (e = var "x": not a value)
theorem w6c3_55 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.eraseExpr_eq_val 2 :=
  fun h => by obtain ⟨_, hw, _⟩ := @h (.var "x") i0; cases hw

-- `Iris.HeapLang.toVal_erase_some` idx 2: necessary (e = var "x": toVal e = none)
theorem w6c3_56 : ¬ drop0% Iris.HeapLang.toVal_erase_some 2 :=
  fun h => by obtain ⟨_, hw, _⟩ := @h (.var "x") i0; simp [ToVal.toVal] at hw

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.eraseBaseLit_inj_of_unboxed` idx 2: necessary (l1 = prophecy p, l2 = poison: both erase to poison)
theorem w6c3_57 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.eraseBaseLit_inj_of_unboxed 2 :=
  fun h => absurd (@h (.prophecy pid) .poison rfl) (by simp)

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.eraseBaseLit_inj_of_unboxed` idx 3: necessary (l1 = #0, l2 = #1 (unboxed, different))
theorem w6c3_58 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.eraseBaseLit_inj_of_unboxed 3 :=
  fun h => absurd (@h (.int 0) (.int 1) (.inl rfl)) (by simp)

-- `Iris.HeapLang.eraseVal_inj_iff` idx 2: necessary (v1 = #(prophecy p), v2 = #poison: equal erasures, different values)
theorem w6c3_59 : ¬ drop0% Iris.HeapLang.eraseVal_inj_iff 2 :=
  fun h => absurd ((@h (.lit (.prophecy pid)) (.lit .poison)).mp rfl) (by simp)

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.eraseVal_eq_lit` idx 2: necessary (v = injL #0: not a literal)
theorem w6c3_60 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.eraseVal_eq_lit 2 :=
  fun h => by obtain ⟨_, hv, _⟩ := @h (.injL i0) (.int 0); cases hv

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.eraseVal_eq_lit_of_ne_poison` idx 2: necessary (l = poison, v = #(prophecy p): erases to #poison but differs)
theorem w6c3_61 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.eraseVal_eq_lit_of_ne_poison 2 :=
  fun h => absurd (@h (.lit (.prophecy pid)) .poison rfl) (by simp)

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.eraseVal_eq_lit_of_ne_poison` idx 3: necessary (v = #0, l = 1)
theorem w6c3_62 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.eraseVal_eq_lit_of_ne_poison 3 :=
  fun h => absurd (@h i0 (.int 1) (by simp)) (by simp)

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.eraseState_get?_some_some` idx 3: necessary (σ = empty state)
theorem w6c3_63 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.eraseState_get?_some_some 3 :=
  fun h => by obtain ⟨_, hg, _⟩ := @h default l0 i0; rw [d_get] at hg; cases hg

-- `Rocq.heap_lang.erased_base_step_base_step_AllocN` idx 4: necessary (n = 0: allocN(#0, _) has no base step)
theorem w6c3_64 : ¬ drop0% Rocq.heap_lang.erased_base_step_base_step_AllocN 4 :=
  fun h => by
    obtain ⟨_, _, _, _, hb, _⟩ := h 0 i0 default l0 (fun _ _ _ => rfl)
    exact an_nb i0 default _ _ _ _ hb

-- `Rocq.heap_lang.erased_base_step_base_step_AllocN` idx 5: necessary (n = 1, l allocated in σ: the base step must allocate a fresh l' and erasure forces l' = l)
theorem w6c3_65 : ¬ drop0% Rocq.heap_lang.erased_base_step_base_step_AllocN 5 :=
  fun h => by
    obtain ⟨_, _, _, _, hb, he, _⟩ := h 1 i0 (σ1 i0) l0 (by decide)
    cases hb with
    | allocNS _ _ _ l' _ hfr =>
      obtain rfl : l' = l0 := by cases he; rfl
      have h0 := hfr 0 (by decide) (by decide)
      change (σ1 i0).get? l0 = none at h0
      rw [σ1_get] at h0; cases h0

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.erased_baseStep_baseStep_AllocN` idx 4: necessary (n = 0: allocN(#0, _) has no base step)
theorem w6c3_66 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.erased_baseStep_baseStep_AllocN 4 :=
  fun h => by
    obtain ⟨_, _, _, _, hb, _⟩ := h 0 i0 default l0 (fun _ _ _ => rfl)
    exact an_nb i0 default _ _ _ _ hb

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.erased_baseStep_baseStep_AllocN` idx 5: necessary (n = 1, l allocated in σ: the base step must allocate a fresh l' and erasure forces l' = l)
theorem w6c3_67 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.erased_baseStep_baseStep_AllocN 5 :=
  fun h => by
    obtain ⟨_, _, _, _, hb, he, _⟩ := h 1 i0 (σ1 i0) l0 (by decide)
    cases hb with
    | allocNS _ _ _ l' _ hfr =>
      obtain rfl : l' = l0 := by cases he; rfl
      have h0 := hfr 0 (by decide) (by decide)
      change (σ1 i0).get? l0 = none at h0
      rw [σ1_get] at h0; cases h0

-- `Rocq.heap_lang.erased_base_step_base_step_Free` idx 3: necessary (σ = empty heap: no base step)
theorem w6c3_68 : ¬ drop0% Rocq.heap_lang.erased_base_step_base_step_Free 3 :=
  fun h => by
    obtain ⟨_, _, _, _, hb, _⟩ := h l0 i0 default
    cases hb with
    | freeS _ _ _ hg => rw [d_get] at hg; cases hg

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.erased_baseStep_baseStep_Free` idx 3: necessary (σ = empty heap: no base step)
theorem w6c3_69 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.erased_baseStep_baseStep_Free 3 :=
  fun h => by
    obtain ⟨_, _, _, _, hb, _⟩ := h l0 i0 default
    cases hb with
    | freeS _ _ _ hg => rw [d_get] at hg; cases hg

-- `Rocq.heap_lang.erased_base_step_base_step_Load` idx 3: necessary (σ = empty heap: no base step)
theorem w6c3_70 : ¬ drop0% Rocq.heap_lang.erased_base_step_base_step_Load 3 :=
  fun h => by
    obtain ⟨_, _, _, _, hb, _⟩ := h l0 default i0
    cases hb with
    | loadS _ _ _ hg => rw [d_get] at hg; cases hg

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.erased_baseStep_baseStep_Load` idx 3: necessary (σ = empty heap: no base step)
theorem w6c3_71 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.erased_baseStep_baseStep_Load 3 :=
  fun h => by
    obtain ⟨_, _, _, _, hb, _⟩ := h l0 default i0
    cases hb with
    | loadS _ _ _ hg => rw [d_get] at hg; cases hg

-- `Rocq.heap_lang.erased_base_step_base_step_Xchg` idx 4: necessary (σ = empty heap: no base step)
theorem w6c3_72 : ¬ drop0% Rocq.heap_lang.erased_base_step_base_step_Xchg 4 :=
  fun h => by
    obtain ⟨_, _, _, _, hb, _⟩ := h l0 i0 i0 default
    cases hb with
    | xchgS _ _ _ _ hg => rw [d_get] at hg; cases hg

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.erased_baseStep_baseStep_Xchg` idx 4: necessary (σ = empty heap: no base step)
theorem w6c3_73 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.erased_baseStep_baseStep_Xchg 4 :=
  fun h => by
    obtain ⟨_, _, _, _, hb, _⟩ := h l0 i0 i0 default
    cases hb with
    | xchgS _ _ _ _ hg => rw [d_get] at hg; cases hg

-- `Rocq.heap_lang.erased_base_step_base_step_Store` idx 4: necessary (σ = empty heap: no base step)
theorem w6c3_74 : ¬ drop0% Rocq.heap_lang.erased_base_step_base_step_Store 4 :=
  fun h => by
    obtain ⟨_, _, _, _, hb, _⟩ := h l0 i0 i0 default
    cases hb with
    | storeS _ _ _ _ hg => rw [d_get] at hg; cases hg

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.erased_baseStep_baseStep_Store` idx 4: necessary (σ = empty heap: no base step)
theorem w6c3_75 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.erased_baseStep_baseStep_Store 4 :=
  fun h => by
    obtain ⟨_, _, _, _, hb, _⟩ := h l0 i0 i0 default
    cases hb with
    | storeS _ _ _ _ hg => rw [d_get] at hg; cases hg

-- `Rocq.heap_lang.erased_base_step_base_step_FAA` idx 4: necessary (σ = empty heap: no base step)
theorem w6c3_76 : ¬ drop0% Rocq.heap_lang.erased_base_step_base_step_FAA 4 :=
  fun h => by
    obtain ⟨_, _, _, _, hb, _⟩ := h l0 0 0 default
    cases hb with
    | faaS _ _ _ _ hg => rw [d_get] at hg; cases hg

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.erased_baseStep_baseStep_FAA` idx 4: necessary (σ = empty heap: no base step)
theorem w6c3_77 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.erased_baseStep_baseStep_FAA 4 :=
  fun h => by
    obtain ⟨_, _, _, _, hb, _⟩ := h l0 0 0 default
    cases hb with
    | faaS _ _ _ _ hg => rw [d_get] at hg; cases hg

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.erased_baseStep_baseStep_CmpXchg` idx 6: necessary (σ = empty heap, b = (vl = v): no base step)
theorem w6c3_78 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.erased_baseStep_baseStep_CmpXchg 6 :=
  fun h => by
    obtain ⟨_, _, _, _, hb, _⟩ := h l0 i0 i0 default i0 true rfl rfl
    cases hb with
    | cmpXchgS _ _ _ _ _ _ hg => rw [d_get] at hg; cases hg

-- `Rocq.heap_lang.erased_base_step_base_step_CmpXchg` idx 7: necessary (l ↦ (#0,#0) = v (not compare-safe): the original CAS is stuck)
theorem w6c3_79 : ¬ drop0% Rocq.heap_lang.erased_base_step_base_step_CmpXchg 7 :=
  fun h => by
    obtain ⟨_, _, _, _, hb, _⟩ := h l0 vp i0 (σ1 vp) vp true (by simp [σ1_get, eraseVal, eraseBaseLit]) (by decide)
    exact cx_nb vp i0 rfl _ _ _ _ hb

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.erased_baseStep_baseStep_CmpXchg` idx 7: necessary (l ↦ (#0,#0) = v (not compare-safe): the original CAS is stuck)
theorem w6c3_80 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.erased_baseStep_baseStep_CmpXchg 7 :=
  fun h => by
    obtain ⟨_, _, _, _, hb, _⟩ := h l0 vp i0 (σ1 vp) vp true (by simp [σ1_get, eraseVal, eraseBaseLit]) (by decide)
    exact cx_nb vp i0 rfl _ _ _ _ hb

-- `Rocq.heap_lang.erased_base_step_base_step_CmpXchg` idx 8: necessary (l ↦ #0, v = #0, b = false: the original CAS succeeds with true)
theorem w6c3_81 : ¬ drop0% Rocq.heap_lang.erased_base_step_base_step_CmpXchg 8 :=
  fun h => by
    obtain ⟨_, _, _, _, hb, he, _⟩ := h l0 i0 i0 (σ1 i0) i0 false (by simp [σ1_get, eraseVal, eraseBaseLit]) rfl
    cases hb with
    | cmpXchgS _ _ _ vl _ b hg hc hd =>
      rw [σ1_get] at hg; cases hg; subst hd
      cases he

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.erased_baseStep_baseStep_CmpXchg` idx 8: necessary (l ↦ #0, v = #0, b = false: the original CAS succeeds with true)
theorem w6c3_82 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.erased_baseStep_baseStep_CmpXchg 8 :=
  fun h => by
    obtain ⟨_, _, _, _, hb, he, _⟩ := h l0 i0 i0 (σ1 i0) i0 false (by simp [σ1_get, eraseVal, eraseBaseLit]) rfl
    cases hb with
    | cmpXchgS _ _ _ vl _ b hg hc hd =>
      rw [σ1_get] at hg; cases hg; subst hd
      cases he

-- `Iris.HeapLang.erased_baseStep_baseStep` idx 6: necessary (e1 = var "x": no base step)
theorem w6c3_83 : ¬ drop0% Iris.HeapLang.erased_baseStep_baseStep 6 :=
  fun h => by obtain ⟨_, _, _, _, hb, _⟩ := @h (.var "x") default [] (.var "x") default []; cases hb

-- `Iris.HeapLang.PrimStepMatchedByErasedSteps.fill_ctx` idx 6: necessary (σ2 has a used prophecy id, so it is no erasure)
theorem w6c3_84 : ¬ drop0% Iris.HeapLang.PrimStepMatchedByErasedSteps.fill_ctx 6 :=
  fun h => by obtain ⟨_, _, _, _, _, _, _, _, hst, _⟩ := @h [] (.var "x") default (.var "x") σbad []; exact es_ne _ hst

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.fill_not_val_ne_val` idx 3: necessary (K = [], e' = val #0)
theorem w6c3_85 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.fill_not_val_ne_val 3 :=
  fun h => @h [] (.val i0) i0 rfl

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.notStuck_of_frame` idx 3: necessary (e = var "x" is stuck)
theorem w6c3_86 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.notStuck_of_frame 3 :=
  fun h => var_ns "x" default (@h .fst (.var "x") default)

-- `Iris.HeapLang.fill_eq_snoc` idx 3: necessary (K = [], e' = var "x", e = var "y")
theorem w6c3_87 : ¬ drop0% Iris.HeapLang.fill_eq_snoc 3 :=
  fun h => by
    rcases @h (.var "y") (.var "x") [] with ⟨_, h2⟩ | ⟨K', Ki, hK, _⟩
    · simp at h2
    · simp at hK

-- `Iris.HeapLang.fill_eq_fst` idx 3: necessary (K = [], e' = X = var "x")
theorem w6c3_88 : ¬ drop0% Iris.HeapLang.fill_eq_fst 3 :=
  fun h => by
    rcases @h (.var "x") (.var "x") [] with ⟨_, h2⟩ | ⟨K', hK, _⟩
    · cases h2
    · simp at hK

-- `Iris.HeapLang.fill_eq_pair` idx 4: necessary (K = [], e' = X = Y = var "x")
theorem w6c3_89 : ¬ drop0% Iris.HeapLang.fill_eq_pair 4 :=
  fun h => by
    rcases @h (.var "x") (.var "x") (.var "x") [] with ⟨_, h2⟩ | ⟨K', v, hK, _⟩ | ⟨K', hK, _⟩
    · cases h2
    · simp at hK
    · simp at hK

-- `Iris.HeapLang.fill_eq_resolve` idx 5: necessary (K = [resolveM e0 v2], e' = val v1 (a value hole))
theorem w6c3_90 : ¬ drop0% Iris.HeapLang.fill_eq_resolve 5 :=
  fun h => by
    rcases @h (.var "x") i0 i0 [.resolveM (.var "x") i0] (.val i0) rfl with ⟨hK, _⟩ | ⟨K', Ki, hK, _⟩
    · simp at hK
    · have := congrArg List.getLast? hK; simp at this

-- `Iris.HeapLang.fill_eq_resolve` idx 6: necessary (K = [], e' = var "x")
theorem w6c3_91 : ¬ drop0% Iris.HeapLang.fill_eq_resolve 6 :=
  fun h => by
    rcases @h (.var "x") i0 i0 [] (.var "x") rfl with ⟨_, h2⟩ | ⟨K', Ki, hK, _⟩
    · cases h2
    · simp at hK

-- `Iris.HeapLang.fill_to_resolve` idx 5: necessary (K = [resolveM e0 v2], e' = val v1 (a value hole))
theorem w6c3_92 : ¬ drop0% Iris.HeapLang.fill_to_resolve 5 :=
  fun h => by
    rcases @h (.var "x") i0 i0 [.resolveM (.var "x") i0] (.val i0) rfl with hK | ⟨K', Ki, hK⟩
    · simp at hK
    · have := congrArg List.getLast? hK; simp at this

-- `Iris.HeapLang.fill_to_resolve` idx 6: necessary (K = [fst], e' = var "x")
theorem w6c3_93 : ¬ drop0% Iris.HeapLang.fill_to_resolve 6 :=
  fun h => by
    rcases @h (.var "x") i0 i0 [.fst] (.var "x") rfl with hK | ⟨K', Ki, hK⟩
    · simp at hK
    · have := congrArg List.getLast? hK; simp at this

-- `Iris.HeapLang.erase_eq_fill_item` idx 3: necessary (e1 = newProph, erased to (λ_, poison) #(); Ki = appL #(), X = the lambda value)
theorem w6c3_94 : ¬ drop0% Iris.HeapLang.erase_eq_fill_item 3 :=
  fun h => by
    rcases @h .newProph _ (.appL (.lit .unit)) rfl with ⟨Ki, ei, he, _⟩ | ⟨hK, _⟩
    · cases Ki <;> simp [ECtxItem.fill] at he
    · cases hK

-- `Iris.HeapLang.erase_eq_fill_item` idx 4: necessary (e1 = var "y", Ki = snd, X = var "x")
theorem w6c3_95 : ¬ drop0% Iris.HeapLang.erase_eq_fill_item 4 :=
  fun h => by
    rcases @h (.var "y") (.var "x") .snd rfl with ⟨Ki, ei, he, _⟩ | ⟨hK, _⟩
    · cases Ki <;> simp [ECtxItem.fill] at he
    · cases hK

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.pureStepIn` idx 3: necessary (K = [], e1 = #0, e2 = #1: values take no pure step)
theorem w6c3_96 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.pureStepIn 3 :=
  fun h => absurd (val_rtc (@h [] (.val i0) (.val i1))) (fun he => by cases he)

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.notStuck_resolve_inv` idx 4: necessary (e0 = var "x" is stuck)
theorem w6c3_97 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.notStuck_resolve_inv 4 :=
  fun h => var_ns "x" default (@h (.var "x") i0 i0 default).1

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.baseStep_pair_inv` idx 7: necessary (X = var "x")
theorem w6c3_98 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.baseStep_pair_inv 7 :=
  fun h => by obtain ⟨_, _, hx, _⟩ := @h (.var "x") (.var "x") (.var "x") default default [] []; cases hx

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.exists_val_of_baseStep_val` idx 11: necessary (e = fst((#0,#0)) steps to a value, e2 = var "x")
theorem w6c3_99 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.exists_val_of_baseStep_val 11 :=
  fun h => by obtain ⟨_, hw⟩ := @h efst (.var "x") i0 default default default default [] [] [] [] (.fstS i0 i0 default); cases hw

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.exists_val_of_baseStep_val` idx 12: necessary (e = if #true then var "x" else var "x" steps to var "x")
theorem w6c3_100 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.exists_val_of_baseStep_val 12 :=
  fun h => by
    obtain ⟨_, hw⟩ := @h (.if (.val (.lit (.bool true))) (.var "x") (.var "x")) (.var "x") i0 default default default default
      [] [] [] [] (.ifTrueS _ _ default)
    cases hw

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.resolve_baseStep_inv` idx 8: necessary (e = fst((#0,#0)), v1 = #0 (not a prophecy))
theorem w6c3_101 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.resolve_baseStep_inv 8 :=
  fun h => by obtain ⟨_, _, hv, _⟩ := @h efst _ i0 i0 default default [] [] (.fstS i0 i0 default); cases hv

-- `Iris.HeapLang.erased_primStep_primStep` idx 6: necessary (e1 = fst((#0,#0)) (not stuck), σ2 has a used prophecy id (no erasure))
theorem w6c3_102 : ¬ drop0% Iris.HeapLang.erased_primStep_primStep 6 :=
  fun h => by obtain ⟨_, _, _, _, _, _, _, _, hst, _⟩ := @h efst default [] (.var "x") σbad [] efst_ns; exact es_ne _ hst

-- `Iris.HeapLang.baseStep_erased_primStep` idx 6: necessary (e1 = var "x": no prim step)
theorem w6c3_103 : ¬ drop0% Iris.HeapLang.baseStep_erased_primStep 6 :=
  fun h => by obtain ⟨_, _, _, hs⟩ := @h (.var "x") default [] (.var "x") default []; exact var_irr "x" _ _ _ _ _ hs

-- `Iris.HeapLang.reducible_erased_reducible` idx 2: necessary (e = var "x": not reducible)
theorem w6c3_104 : ¬ drop0% Iris.HeapLang.reducible_erased_reducible 2 :=
  fun h => by obtain ⟨_, _, _, _, hs⟩ := @h (.var "x") default; exact var_irr "x" _ _ _ _ _ hs

-- `Iris.HeapLang.pureStep_tp_safe` idx 4: necessary (t1 = t2 = [var "x"], e1 = var "x" (stuck))
theorem w6c3_105 : ¬ drop0% Iris.HeapLang.pureStep_tp_safe 4 :=
  fun h => var_ns "x" _ (@h [.var "x"] [.var "x"] (.var "x") default (.cons .refl .nil) (List.mem_singleton_self _))

-- `Iris.HeapLang.pureStep_tp_safe` idx 5: necessary (t2 = [], t1 = [var "x"])
theorem w6c3_106 : ¬ drop0% Iris.HeapLang.pureStep_tp_safe 5 :=
  fun h => var_ns "x" _ (@h [.var "x"] [] (.var "x") default (fun _ hm => absurd hm (List.not_mem_nil)) (List.mem_singleton_self _))

-- `Iris.HeapLang.pureStep_tp_safe` idx 6: necessary (t1 = t2 = [], e1 = var "x")
theorem w6c3_107 : ¬ drop0% Iris.HeapLang.pureStep_tp_safe 6 :=
  fun h => var_ns "x" _ (@h [] [] (.var "x") default (fun _ hm => absurd hm (List.not_mem_nil)) .nil)

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.pureSteps_set` idx 2: necessary (t = [], t' = [#0]: lengths differ)
theorem w6c3_108 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.pureSteps_set 2 :=
  fun h => by have := (@h [] [.val i0] 0 (.val i0) (.val i0) .refl).length_eq; simp at this

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.pureSteps_set` idx 6: necessary (t = t' = [#0], e' = #0, eo' = #1: values take no pure step)
theorem w6c3_109 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.pureSteps_set 6 :=
  fun h => by
    have := @h [.val i0] [.val i0] (.cons .refl .nil) 0 (.val i0) (.val i1)
    simp at this
    exact absurd (val_rtc this) (fun he => by cases he)

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.getElem?_eraseTp` idx 3: necessary (t = [])
theorem w6c3_110 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.getElem?_eraseTp 3 :=
  fun h => by obtain ⟨_, hg, _⟩ := @h [] 0 (.var "x"); cases hg

-- `Iris.HeapLang.erasure` idx 3: necessary (e = #0, φ = False: the erased program is the value #0, whose result must satisfy φ)
theorem w6c3_111 : ¬ drop0% Iris.HeapLang.erasure 3 :=
  fun h => by
    obtain ⟨_, _, _, _, hf⟩ := (@h (.val i0) default (fun _ _ => False)).adequate_result [] _ i0 .refl
    exact hf

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.PrimStepMatchedByErasedSteps.fill_item` idx 7: necessary (σ2 has a used prophecy id, so it is no erasure)
theorem w6c3_112 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.PrimStepMatchedByErasedSteps.fill_item 7 :=
  fun h => by obtain ⟨_, _, _, _, _, _, _, _, hst, _⟩ := @h .fst (.var "x") (.var "x") [] default σbad []; exact es_ne _ hst

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.resolve_pairL_primStepMatched` idx 9: necessary (r0 = fst((#0,#0)), w1 = #(prophecy p) with p used in σ1 (not stuck), σ2 has a used prophecy id (no erasure))
theorem w6c3_113 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.resolve_pairL_primStepMatched 9 :=
  fun h => by obtain ⟨_, _, _, _, _, _, _, _, hst, _⟩ := @h efst (.var "x") (.lit (.prophecy pid)) i0 [] σbad σbad [] eres_ns; exact es_ne _ hst

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.resolve_baseStep_inv` idx 9: necessary (e = fst((#0,#0)), v1 = #(prophecy p), p used (resolve not stuck), e2 = var "x")
theorem w6c3_114 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.resolve_baseStep_inv 9 :=
  fun h => by obtain ⟨_, _, _, _, hv⟩ := @h efst (.var "x") (.lit (.prophecy pid)) i0 σbad default [] [] eres_ns; cases hv

-- `Iris.HeapLang.erased_primStep_primStep` idx 7: necessary (e1 = resolve(#0, #0, #0) is stuck, its erasure fst(fst(((#0,#0),#0))) steps)
theorem w6c3_115 : ¬ drop0% Iris.HeapLang.erased_primStep_primStep 7 :=
  fun h => by
    have hs : ((eraseExpr (Exp.resolve (.val i0) (.val i0) (.val i0)), eraseState default) -<[]>->
        (ProgramLogic.fill [ECtxItem.pairL i0, ECtxItem.fst, ECtxItem.fst] (Exp.val (Val.pair i0 i0)), eraseState default, ([] : List Exp))) :=
      EctxLanguage.fill_primStep [ECtxItem.pairL i0, ECtxItem.fst, ECtxItem.fst] (EctxLanguage.primStep_of_baseStep (BaseStep.pairS i0 i0 _))
    obtain ⟨_, _, _, _, _, hs2, _⟩ := @h (Exp.resolve (.val i0) (.val i0) (.val i0)) default [] _ _ _ hs
    exact Iris.HeapLang.Resolve_3_vals_unsafe i0 i0 i0 default (.inr ⟨_, _, _, _, hs2⟩)

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.erasure_cut` idx 5: necessary (e = #0 (adequate by heap_adequacy), ρ2 = ([], σ) with a used prophecy id: no erasure)
theorem w6c3_116 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.erasure_cut 5 :=
  fun h => by
    have ad := Iris.HeapLang.heap_adequacy (GF := HS) (.val i0) default (fun _ => True) fun {_} =>
      wand_intro (sep_elim_left.trans ((pure_intro trivial).trans (wp_value' (Φ := fun _ => iprop(⌜True⌝)) (v := i0))))
    obtain ⟨_, _, _, hst, _⟩ := @h (.val i0) default _ ad ([], σbad)
    exact es_ne _ hst.symm

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.resolve_pairL_primStepMatched` idx 8: necessary (r0 = fst((#0,#0)) steps (hm holds with Ks = []), but w1 = #0 is no prophecy, so resolve(r0, #0, _) is stuck)
theorem w6c3_117 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.resolve_pairL_primStepMatched 8 :=
  fun h => by
    have hm : PrimStepMatchedByErasedSteps efst default (ProgramLogic.fill [] (Exp.val i0)) (eraseState default) [] :=
      ⟨Exp.val i0, default, [], [], Exp.val i0, EctxLanguage.primStep_of_baseStep (.fstS i0 i0 default), .refl, rfl, rfl, rfl⟩
    obtain ⟨_, _, _, _, _, hs, _⟩ := @h efst (.val i0) i0 i0 [] default (eraseState default) [] hm
    exact res0_irr i0 _ _ _ _ _ hs

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.fill_resolve_frames_pureSteps` idx 5: necessary (Ks = [], e = var "x" (the framed term is stuck), e' = var "y")
theorem w6c3_118 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.fill_resolve_frames_pureSteps 5 :=
  fun h => by
    have H := rtc_stuck (frames_np i0 i0 "x") (@h (.var "x") (.var "y") [] i0 i0)
    first | exact absurd H (by decide) | (simp [eraseResolve, ProgramLogic.fill, fillItem, ECtxItem.fill] at H) | cases H

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.resolve_fst_primStepMatched` idx 12: necessary (r0 = fst((#0,#0)), r1 = #(prophecy p) used, r2 = #0; erased step fst((#0,#0)) → #0 with Ks = [] (unrelated to the resolve); target fst(#0) is stuck and no value)
theorem w6c3_119 : ¬ drop0% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.resolve_fst_primStepMatched 12 :=
  fun h => by
    have IH : ∀ {K' : List ECtxItem} {e0 : Exp}, K'.length ≤ ([] : List ECtxItem).length →
        eraseExpr e0 = ProgramLogic.fill K' efst → PrimStep.NotStuck (e0, σbad) →
        PrimStepMatchedByErasedSteps e0 σbad (ProgramLogic.fill K' (Exp.val i0)) (eraseState σbad) [] := by
      intro K' e0 hlen he _
      cases K' with
      | cons _ _ => simp at hlen
      | nil =>
        cases e0 <;> simp [eraseExpr, eraseResolve, erasedNewProph, ProgramLogic.fill] at he
        rename_i e
        obtain ⟨w, rfl, hw⟩ := (priv% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.eraseExpr_eq_val) he
        cases w <;> simp [eraseVal] at hw
        rename_i a b
        obtain ⟨ha, hb⟩ := hw
        have ha' := (priv% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.eraseVal_eq_lit_of_ne_poison) (v := a) (l := .int 0) (by simp) ha
        have hb' := (priv% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.eraseVal_eq_lit_of_ne_poison) (v := b) (l := .int 0) (by simp) hb
        subst ha' hb'
        exact ⟨_, _, _, _, _, EctxLanguage.primStep_of_baseStep (.fstS i0 i0 σbad), .refl, rfl, rfl, rfl⟩
    obtain ⟨e2, _, _, _, e3, hs, hp, hx, _⟩ := @h efst (.val (.lit (.prophecy pid))) (.val i0) [] efst (.val i0) σbad
      (eraseState σbad) [] [] (.fstS i0 i0 _) eres_ns IH
    have hb := EctxLanguage.baseStep_of_primStep hs (res0_sr _ _)
    cases hb
    have := rtc_stuck fst0_np hp
    subst this
    cases hx

-- `_private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.resolve_fst_primStepMatched` idx 13: removable (IHapp unneeded: the erased base step under fill (Ks ++ [fst]) is a prim step of the erased resolve, so the public theorem erased_primStep_primStep (with hns) gives the conclusion directly)
theorem w6c3_120 : drop% _private.Iris.HeapLang.ProphErasure.«0».Iris.HeapLang.resolve_fst_primStepMatched 13 :=
  by
    intro r0 r1 r2 Ks e1' e2' σ1 σ2 κ efs bstep hns heq_e
    refine Iris.HeapLang.erased_primStep_primStep (κ := κ) ?_ hns
    have hs : (ProgramLogic.fill (Ks ++ [ECtxItem.fst]) e1', eraseState σ1) -<κ>->
        (ProgramLogic.fill (Ks ++ [ECtxItem.fst]) e2', σ2, efs) :=
      EctxLanguage.fill_primStep _ (EctxLanguage.primStep_of_baseStep bstep)
    have he : ProgramLogic.fill (Ks ++ [ECtxItem.fst]) e1' = eraseExpr (Exp.resolve r0 r1 r2) := by
      rw [Iris.HeapLang.fill_snoc, ← heq_e]; rfl
    rw [he] at hs
    exact hs

end W6c3
