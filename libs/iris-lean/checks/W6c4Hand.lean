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
namespace W6c4
open Iris Iris.BI COFE

/-- Every slot of the global functor is the constant functor on disjoint copsets (error invalid). -/
def GFc : BundledGFunctors.{0, 0, 0} := fun _ => ⟨constOF CoPsetDisjL⟩
instance elemC : ElemG GFc (constOF CoPsetDisjL) := { τ := 0, transp := rfl }
abbrev ce : CoPsetDisjL := .valid ∅
abbrev cr : CoPsetDisjL := .error

theorem unf (x : CoPsetDisjL) : (IProp.unfoldi (FF := GFc) (τ := 0)).f x = x := rfl
theorem bun (x : CoPsetDisjL) : elemC.bundle (T := IProp GFc) x = x := rfl
theorem sg_at (γ : GName) (v : CoPsetDisjL) :
    (iSingleton (GF := GFc) (constOF CoPsetDisjL) γ v (ElemG.τ GFc (constOF CoPsetDisjL))).car γ = some v := by
  unfold iSingleton; rw [dif_pos rfl]; exact GenMap.singleton_map_in _ _
theorem cr_inv {n} : ¬ ✓{n} cr := DisjointLeibnizSet.not_validN_invalid

theorem bupd_false_unsound {GF : BundledGFunctors} (H : ⊢ (|==> iprop(⌜False⌝) : IProp GF)) : False :=
  pure_soundness (PROP := IProp GF) (UPred.bupd_soundness H)
theorem cvf : (UPred.cmraValid cr : IProp GFc) ⊢ iprop(⌜False⌝) := fun n x h => cr_inv h
abbrev sgc (γ : GName) (v : CoPsetDisjL) : IResUR GFc := iSingleton (GF := GFc) (constOF CoPsetDisjL) γ v
theorem sg_ne {γ γ' : GName} (v : CoPsetDisjL) (h : γ' ≠ γ) :
    ((sgc γ v) (ElemG.τ GFc (constOF CoPsetDisjL))).car γ' = none := iSingleton_free_at_ne h
/-- error at name 0 in every slot -/
def allBad : IResUR GFc := fun _ => GenMap.singleton 0 cr
theorem empty_disj : (∅ : CoPset) ## ∅ := fun _ ⟨h1, _⟩ => CoPset.mem_empty h1
theorem disj_empty (s : CoPset) : s ## ∅ := fun _ ⟨_, h⟩ => CoPset.mem_empty h
theorem full_not_disj : ¬ (CoPset.full ## CoPset.full) := fun hd => hd .xH ⟨rfl, rfl⟩
theorem ce_ce_valid {n} : ✓{n} (ce • ce) := by
  change ✓{n} (if (∅ : CoPset) ## ∅ then _ else _); rw [if_pos empty_disj]; trivial
theorem s_valid {n γ} {v : CoPsetDisjL} (h : ✓{n} v) : ✓{n} sgc γ v := validN_iSingleton.mpr h
theorem alloc_ce : ⊢ (|==> ∃ γ, iOwn (GF := GFc) (F := constOF CoPsetDisjL) γ ce : IProp GFc) :=
  iOwn_alloc (GF := GFc) (F := constOF CoPsetDisjL) ce trivial
theorem own_cr_false (γ) : iOwn (GF := GFc) (F := constOF CoPsetDisjL) γ cr ⊢ iprop(⌜False⌝) :=
  iOwn_cmraValid.trans cvf

theorem cece_valid {n} : ✓{n} ((ce • ce) • ce) := by
  change ✓{n} ((if (∅ : CoPset) ## ∅ then DisjointLeibnizSet.valid (∅ ∪ ∅) else DisjointLeibnizSet.error : CoPsetDisjL) • ce)
  rw [if_pos empty_disj]
  change ✓{n} (if (∅ ∪ ∅ : CoPset) ## ∅ then _ else _)
  rw [if_pos (disj_empty _)]; trivial
theorem alloc_2 : ⊢ (|==> ∃ γ, iOwn (GF := GFc) (F := constOF CoPsetDisjL) γ ce ∗ iOwn (GF := GFc) (F := constOF CoPsetDisjL) γ ce : IProp GFc) :=
  (iOwn_alloc (GF := GFc) (F := constOF CoPsetDisjL) (ce • ce) (ORA.valid_iff_validN.mpr fun _ => ce_ce_valid)).trans
    (BIUpdate.mono (BI.exists_mono fun γ => (iOwn_op (GF := GFc) (F := constOF CoPsetDisjL) (γ := γ) (a1 := ce) (a2 := ce)).mp))
theorem alloc_3 : ⊢ (|==> ∃ γ, iOwn (GF := GFc) (F := constOF CoPsetDisjL) γ ce ∗ iOwn (GF := GFc) (F := constOF CoPsetDisjL) γ ce ∗
    iOwn (GF := GFc) (F := constOF CoPsetDisjL) γ ce : IProp GFc) :=
  (iOwn_alloc (GF := GFc) (F := constOF CoPsetDisjL) ((ce • ce) • ce) (ORA.valid_iff_validN.mpr fun _ => cece_valid)).trans
    (BIUpdate.mono (BI.exists_mono fun γ => (iOwn_op (GF := GFc) (F := constOF CoPsetDisjL) (γ := γ) (a1 := ce • ce) (a2 := ce)).mp.trans
      ((BI.sep_mono_left (iOwn_op (GF := GFc) (F := constOF CoPsetDisjL) (γ := γ) (a1 := ce) (a2 := ce)).mp).trans BI.sep_assoc.1)))
/-- valid in slot 0, error at name 0 in every other slot -/
def mf1 : IResUR GFc := fun τ => if τ = 0 then GenMap.empty else GenMap.singleton 0 cr
instance ceCore : ORA.CoreId ce := ⟨rfl⟩

/-- Discrete ORA on booleans: every product is false, only true valid, no core, order = inclusion
(x ≼ₒ y ↔ y = false): IncOrd and OrdInc, not OrderRefl, not IsTotal (true is below no valid element). -/
structure XB where b : Bool
instance : COFE XB := COFE.ofDiscrete _
instance : OFE.Discrete XB := ⟨fun h => h⟩
def xbData : DiscreteORAData XB where
  pcore _ := none
  op _ _ := ⟨false⟩
  Valid x := x.b = true
  Order _ y := y.b = false
  assoc _ _ _ := rfl
  comm _ _ := rfl
  pcore_op_left _ _ h := nomatch h
  pcore_idem _ _ h := nomatch h
  valid_op_left _ _ h := nomatch h
  ord_trans _ _ _ _ h := h
  op_mono_left _ _ _ _ := rfl
  valid_of_ord _ _ h hv := absurd (h.symm.trans hv) (by decide)
  pcore_mono _ _ _ _ h := nomatch h
  pcore_order_op _ _ h := nomatch h
  pcore_increasing _ _ h := nomatch h
  increasing_closed _ _ _ _ _ := rfl
instance xbORA : ORA XB := ORA.ofDiscreteORAData xbData
instance : ORA.Discrete XB := ORA.ofDiscreteORAData_discrete xbData
abbrev xt : XB := ⟨true⟩
abbrev xf : XB := ⟨false⟩
theorem xb_eq_f {y : XB} (h : y.b = false) : y = xf := by cases y; cases h; rfl
instance : IncOrd XB := ⟨fun {_ y} ⟨_, e⟩ => show y.b = false from congrArg XB.b (show y = xf from e)⟩
instance : OrdInc XB where
  ord_inc {x y} h := ⟨x, show y = xf from xb_eq_f h⟩
  ordN_incN {_ x y} h := ⟨x, show y = xf from xb_eq_f h⟩
def GFx : BundledGFunctors.{0, 0, 0} := fun _ => ⟨constOF XB⟩
instance elemX : ElemG GFx (constOF XB) := { τ := 0, transp := rfl }
theorem alloc_xt : ⊢ (|==> ∃ γ, iOwn (GF := GFx) (F := constOF XB) γ xt : IProp GFx) :=
  iOwn_alloc (GF := GFx) (F := constOF XB) xt rfl
theorem xv (c : XB) : (UPred.cmraValid c : IProp GFx) ⊢ iprop(⌜c.b = true⌝) := fun _ _ h => h
theorem xo (c : XB) : (iprop(xt ≼ₒ c) : IProp GFx) ⊢ iprop(⌜c.b = false⌝) := fun _ _ h => h
theorem xi (c : XB) : (iprop(xt ≼ c) : IProp GFx) ⊢ iprop(⌜c.b = false⌝) := fun _ _ h => by
  obtain ⟨_, ⟨z, rfl⟩, hz⟩ := h
  exact congrArg XB.b (show c = xf from hz)
theorem xbad {c : XB} : (iprop(⌜c.b = true⌝ ∗ ⌜c.b = false⌝) : IProp GFx) ⊢ iprop(⌜False⌝) := by
  iintro ⟨%h1, %h2⟩; cases h1.symm.trans h2
theorem own_x (γ) (c : XB) : iOwn (GF := GFx) (F := constOF XB) γ c ⊢ iprop(⌜c.b = true⌝) := iOwn_cmraValid.trans (xv c)
theorem own_xf_false (γ) : iOwn (GF := GFx) (F := constOF XB) γ xf ⊢ iprop(⌜False⌝) :=
  (own_x γ xf).trans (BI.pure_mono fun h => Bool.noConfusion h)
theorem xb_no_up (c : XB) (hv : ✓ c) (h1 : xt ≼ₒ c) : False := absurd ((show c.b = true from hv).symm.trans h1) (by decide)
theorem xb_no_inc (c : XB) (hv : ✓ c) (h1 : xt ≼ c) : False := xb_no_up c hv (IncOrd.inc_ord h1)

/-- Discrete total ORA on {e, a, b, bot}: e unit, other products bot, core e, bot invalid,
order = equality plus a ≤ b, x ≤ bot, e ≤ x: IncOrd, OrderRefl, IsTotal, not OrdInc (a ≤ b but a ⋠ b). -/
inductive Y2 | e | a | b | bot deriving DecidableEq
instance : COFE Y2 := COFE.ofDiscrete _
instance : OFE.Discrete Y2 := ⟨fun h => h⟩
def y2op : Y2 → Y2 → Y2
  | .e, x => x
  | x, .e => x
  | _, _ => .bot
def y2ord (x y : Y2) : Prop := x = y ∨ (x = .a ∧ y = .b) ∨ y = .bot ∨ x = .e
instance (x y : Y2) : Decidable (y2ord x y) := by unfold y2ord; infer_instance
def y2Data : DiscreteORAData Y2 where
  pcore _ := some .e
  op := y2op
  Valid x := x ≠ .bot
  Order := y2ord
  assoc x y z := by cases x <;> cases y <;> cases z <;> rfl
  comm x y := by cases x <;> cases y <;> rfl
  pcore_op_left x _ h := by cases h; cases x <;> rfl
  pcore_idem _ _ h := by cases h; rfl
  valid_op_left x y := by cases x <;> cases y <;> decide
  ord_trans x y z := by cases x <;> cases y <;> cases z <;> decide
  op_mono_left x y z := by cases x <;> cases y <;> cases z <;> decide
  valid_of_ord x y := by cases x <;> cases y <;> decide
  pcore_mono _ _ _ _ h := by cases h; exact ⟨.e, rfl, Or.inl rfl⟩
  pcore_order_op _ _ h _ := by cases h; exact ⟨.e, rfl, Or.inl rfl⟩
  pcore_increasing _ _ h y := by cases h; cases y <;> decide
  increasing_closed _ y _ _ z := by cases y <;> cases z <;> decide
instance y2ORA : ORA Y2 := ORA.ofDiscreteORAData y2Data
instance : ORA.Discrete Y2 := ORA.ofDiscreteORAData_discrete y2Data
instance : IncOrd Y2 := ⟨fun {x y} ⟨z, e⟩ => by
  change y = y2op x z at e; subst e; change y2ord x (y2op x z); cases x <;> cases z <;> decide⟩
instance : IsTotal Y2 := ⟨fun _ => ⟨.e, rfl⟩⟩
instance : OrderRefl Y2 := ⟨fun _ => Or.inl rfl⟩
def GFy : BundledGFunctors.{0, 0, 0} := fun _ => ⟨constOF Y2⟩
instance elemY : ElemG GFy (constOF Y2) := { τ := 0, transp := rfl }
abbrev yown (γ : GName) (c : Y2) : IProp GFy := iOwn (GF := GFy) (F := constOF Y2) γ c
theorem alloc_yb : ⊢ (|==> ∃ γ, yown γ .b : IProp GFy) :=
  iOwn_alloc (GF := GFy) (F := constOF Y2) .b (show Y2.b ≠ .bot by decide)
theorem yb_ab (γ) : yown γ .b ⊢ yown γ .a ∧ yown γ .b :=
  BI.and_intro (iOwn_ord_mono (GF := GFy) (F := constOF Y2) (a1 := .b) (a2 := .a) (Or.inr (Or.inl ⟨rfl, rfl⟩))) .rfl
theorem yv (γ) (c : Y2) : yown γ c ⊢ iprop(⌜c ≠ .bot⌝) := iOwn_cmraValid.trans fun _ _ h => h
theorem y_inc (x c : Y2) (hx : x ≠ .e) : (iprop(x ≼ c) : IProp GFy) ⊢ iprop(⌜c = x ∨ c = .bot⌝) := fun _ _ h => by
  obtain ⟨_, ⟨z, rfl⟩, hz⟩ := h
  change c = y2op x z at hz
  have key : c = x ∨ c = .bot := by subst hz; cases x <;> cases z <;> simp_all [y2op]
  exact key
theorem y_incS (x c : Y2) (hx : x ≠ .e) : (iprop(some x ≼ some c) : IProp GFy) ⊢ iprop(⌜c = x ∨ c = .bot⌝) := fun _ _ h => by
  obtain ⟨_, ⟨z, rfl⟩, hz⟩ := h
  rcases z with _ | z
  · change c = x at hz; exact .inl hz
  · change c = y2op x z at hz
    have key : c = x ∨ c = .bot := by subst hz; cases x <;> cases z <;> simp_all [y2op]
    exact key
theorem ybad {c : Y2} : (iprop(⌜c ≠ .bot⌝ ∗ ⌜c = .a ∨ c = .bot⌝ ∗ ⌜c = .b ∨ c = .bot⌝) : IProp GFy) ⊢ iprop(⌜False⌝) := by
  iintro ⟨%h1, %h2, %h3⟩; cases c <;> simp_all
theorem ybad' {c : Y2} : (iprop(⌜c ≠ .bot⌝ ∗ (⌜c = .a ∨ c = .bot⌝ ∧ ⌜c = .b ∨ c = .bot⌝)) : IProp GFy) ⊢ iprop(⌜False⌝) := by
  iintro ⟨%h1, %h2, %h3⟩; cases c <;> simp_all
theorem y_no_common (c' : Y2) (hv : ✓ c') (h1 : Y2.a ≼ c') (h2 : Y2.b ≼ c') : False := by
  obtain ⟨z1, e1⟩ := h1; obtain ⟨z2, e2⟩ := h2
  change c' = y2op .a z1 at e1; change c' = y2op .b z2 at e2
  change c' ≠ .bot at hv
  subst e1; cases z1 <;> cases z2 <;> simp_all [y2op]
instance : Inhabited {x : Bool // True} := ⟨⟨true, trivial⟩⟩
theorem wpure {GF : BundledGFunctors} (X : IProp GF) : iprop(⌜True⌝ -∗ X) ⊢ X :=
  BI.sep_emp.mpr.trans ((BI.sep_mono_right (BI.pure_intro trivial)).trans BI.wand_elim_left)
theorem yforall (γ) : yown γ .b ⊢ iprop(∀ x : Bool, yown γ (bif x then .a else .b)) :=
  BI.forall_intro fun x => by cases x; exact .rfl; exact (yb_ab γ).trans BI.and_elim_l
theorem yforallp (γ) : yown γ .b ⊢ iprop(∀ x : Bool, ⌜True⌝ -∗ yown γ (bif x then .a else .b)) :=
  BI.forall_intro fun x => BI.wand_intro (BI.sep_elim_left.trans (by cases x; exact .rfl; exact (yb_ab γ).trans BI.and_elim_l))

/-- Truncation OFE on naturals (Probe1's TN): 1 and 2 agree at step 0. -/
structure TN where v : Nat
def tnOFE : OFE TN where
  Dist n x y := min x.v (n+1) = min y.v (n+1)
  dist_eqv := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩
  eq_dist' {x y} := ⟨fun h n => h ▸ rfl, fun h => by
      cases x with | mk a => cases y with | mk b =>
      have h' : min a (a+b+1) = min b (a+b+1) := h (a+b)
      simp only [TN.mk.injEq]; omega⟩
  dist_lt {n x y m} h hm := by
    have h' : min x.v (n+1) = min y.v (n+1) := h
    show min x.v (m+1) = min y.v (m+1); omega
/-- Excl TN over the truncation OFE and over the discrete OFE on the same carrier. -/
def exT : ORA (Excl TN) := by letI : OFE TN := tnOFE; exact inferInstance
def exD : ORA (Excl TN) := by letI : OFE TN := OFE.ofDiscrete TN; exact inferInstance
/-- Two more discrete ORAs on XB: op and, all valid, no core, order equality; the same with core true. -/
def xaData : DiscreteORAData XB where
  pcore _ := none
  op x y := ⟨x.b && y.b⟩
  Valid _ := True
  Order := Eq
  assoc x y z := congrArg XB.mk (Bool.and_assoc x.b y.b z.b).symm
  comm x y := congrArg XB.mk (Bool.and_comm x.b y.b)
  pcore_op_left _ _ h := nomatch h
  pcore_idem _ _ h := nomatch h
  valid_op_left _ _ _ := trivial
  ord_trans _ _ _ h1 h2 := h1.trans h2
  op_mono_left _ _ _ h := h ▸ rfl
  valid_of_ord _ _ _ _ := trivial
  pcore_mono _ _ _ _ h := nomatch h
  pcore_order_op _ _ h := nomatch h
  pcore_increasing _ _ h := nomatch h
  increasing_closed _ _ hx hxy := hxy ▸ hx
def xcData : DiscreteORAData XB where
  pcore _ := some ⟨true⟩
  op x y := ⟨x.b && y.b⟩
  Valid _ := True
  Order := Eq
  assoc x y z := congrArg XB.mk (Bool.and_assoc x.b y.b z.b).symm
  comm x y := congrArg XB.mk (Bool.and_comm x.b y.b)
  pcore_op_left x _ h := by cases h; cases x; rfl
  pcore_idem _ _ h := by cases h; rfl
  valid_op_left _ _ _ := trivial
  ord_trans _ _ _ h1 h2 := h1.trans h2
  op_mono_left _ _ _ h := h ▸ rfl
  valid_of_ord _ _ _ _ := trivial
  pcore_mono _ _ _ _ h := by cases h; exact ⟨_, rfl, rfl⟩
  pcore_order_op _ _ h _ := by cases h; exact ⟨_, rfl, rfl⟩
  pcore_increasing _ _ h y := by cases h; cases y; rfl
  increasing_closed _ _ hx hxy := hxy ▸ hx
abbrev RXB := @OFunctor.constOF_RFunctorContractive XB xbORA
abbrev RXA := @OFunctor.constOF_RFunctorContractive XB (ORA.ofDiscreteORAData xaData)
abbrev RXC := @OFunctor.constOF_RFunctorContractive XB (ORA.ofDiscreteORAData xcData)
/-- n = 0 and True agree at step 0 but differ (Probe3). -/
def sp0 : SiProp := { holds := fun n => n = 0, closed := fun h hle => by omega }
def sp1 : SiProp := { holds := fun _ => True, closed := fun h _ => h }
theorem sp_dist0 : sp0 ≡{0}≡ sp1 := by
  intro m hm
  exact ⟨fun _ => trivial, fun _ => by show m = 0; omega⟩
theorem sp_ne : sp0 ≠ sp1 := fun e => by
  have : sp0.holds 1 = sp1.holds 1 := congrArg (·.holds 1) e
  have h1 : sp1.holds 1 := trivial
  rw [← this] at h1
  have h2 : (1 : Nat) = 0 := h1
  exact absurd h2 (by decide)
def GFag : BundledGFunctors.{0, 0, 0} := fun _ => ⟨constOF (Agree SiProp)⟩
instance elemAg : ElemG GFag (constOF (Agree SiProp)) := { τ := 0, transp := rfl }
theorem ag_dist : toAgree sp0 ≡{0}≡ toAgree sp1 := OFE.NonExpansive.ne @sp_dist0
theorem ag_ne : toAgree sp0 ≠ toAgree sp1 := fun e => sp_ne (Agree.toAgree_inj e)

/-- Never holds: differs from sp0 at step 0. -/
def sp2 : SiProp := { holds := fun _ => False, closed := fun h _ => h }
abbrev sgA (γ : GName) (v : Agree SiProp) : IResUR GFag := iSingleton (GF := GFag) (constOF (Agree SiProp)) γ v
theorem ag_no_ub (c' : Agree SiProp) (hv : ✓ c') (h1 : toAgree sp0 ≼ₒ c') (h2 : toAgree sp1 ≼ₒ c') : False := by
  have e := (Agree.valid_ord hv h1).trans (Agree.valid_ord hv h2).symm
  exact sp_ne (OFE.eq_dist.mpr fun n => Agree.toAgree_injN (OFE.eq_dist.mp e n))
theorem ag_valid0 : ✓{0} sgA 0 (toAgree sp0) := validN_iSingleton.mpr Agree.toAgree_validN
theorem ag_own01 : (UPred.ownM (sgA 0 (toAgree sp0)) : IProp GFag).holds 0 ⟨sgA 0 (toAgree sp0), ag_valid0⟩ ∧
    (UPred.ownM (sgA 0 (toAgree sp1)) : IProp GFag).holds 0 ⟨sgA 0 (toAgree sp0), ag_valid0⟩ := by
  have hd : iSingleton (GF := GFag) (constOF (Agree SiProp)) 0 (toAgree sp0) ≡{0}≡ iSingleton (GF := GFag) (constOF (Agree SiProp)) 0 (toAgree sp1) :=
    OFE.NonExpansive.ne (OFE.NonExpansive.ne @sp_dist0)
  have hr := Ordered.ordN_of_ord 0 (OrderRefl.ord_refl (sgA 0 (toAgree sp0)))
  exact ⟨hr, Ordered.ordN_ne hd .rfl hr⟩
theorem ag_not_own2 : ¬ (UPred.ownM (sgA 0 (toAgree sp2)) : IProp GFag).holds 0 ⟨sgA 0 (toAgree sp0), ag_valid0⟩ := fun h => by
  have h3 := h (ElemG.τ GFag (constOF (Agree SiProp))) 0
  change (some (toAgree sp2) : Option (Agree SiProp)) ≼ₒ{0} some (toAgree sp0) at h3
  have h4 : toAgree sp2 ≼ₒ{0} toAgree sp0 := by
    rcases Option.some_ordN_some_iff.mp h3 with h5 | h5
    · exact Ordered.ordN_ne h5.symm .rfl (Ordered.ordN_of_ord 0 (OrderRefl.ord_refl _))
    · exact h5
  have h5 : sp2 ≡{0}≡ sp0 := Agree.toAgree_ordN.mp h4
  exact (h5 (Nat.le_refl 0)).2 rfl

theorem own_not_unit (γ : GName) (x : CoPsetDisjL) :
    ¬ (iOwn (GF := GFc) (F := constOF CoPsetDisjL) γ x).holds 0 ⟨UORA.unit, UORA.unit_valid.validN⟩ := fun h => by
  unfold iOwn at h
  have h3 := h (ElemG.τ GFc (constOF CoPsetDisjL)) γ
  rw [sg_at] at h3
  exact Option.not_some_ordN_none h3
end W6c4

section
open Iris Iris.HeapLang Iris.Std

-- `Iris.HeapLang.BinOp.eval_lit_loc` (hypothesis 3): necessary, op = eq, l = 0, lit = loc 0: eval gives some true, evalLoc gives none
theorem w6c4_1 : ¬ drop0% Iris.HeapLang.BinOp.eval_lit_loc 3 := fun h => by
  have := h .eq ⟨0⟩ (.loc ⟨0⟩)
  simp [BinOp.eval, BinOp.evalLoc, Val.compareSafe, Val.isUnboxed, BaseLit.isUnboxed] at this

-- `Iris.HeapLang.heapArray_disjoint` (hypothesis 3): necessary, vs = [none], m = heapArray 0 [none]
theorem w6c4_2 : ¬ drop0% Iris.HeapLang.heapArray_disjoint 3 := fun h => by
  have := h (l := ⟨0⟩) (vs := [none]) (m := heapArray ⟨0⟩ [none]) ⟨0⟩
  have e : PartialMap.get? (M := HeapF) (heapArray ⟨0⟩ [none]) ⟨0⟩ = some none :=
    get?_heapArray.mpr ⟨0, by simp [loc_add_zero], rfl⟩
  rw [e] at this
  exact this ⟨rfl, rfl⟩

-- `Iris.HeapLang.allocCells_disjoint` (hypothesis 4): necessary, n = 1, m = allocCells 0 1 v
theorem w6c4_3 : ¬ drop0% Iris.HeapLang.allocCells_disjoint 4 := fun h => by
  have := h (l := ⟨0⟩) (n := 1) (v := .lit .unit) (m := allocCells ⟨0⟩ 1 (some (.lit .unit))) ⟨0⟩
  have e : PartialMap.get? (M := HeapF) (allocCells ⟨0⟩ 1 (some (.lit .unit))) ⟨0⟩ = some (some (.lit .unit)) := by
    rw [get?_allocCells, ite_eq_left ⟨0, by decide, by simp [loc_add_zero]⟩]
  simp only [Int.toNat_one] at this
  rw [e] at this
  exact this ⟨rfl, rfl⟩

-- `Iris.HeapLang.State.initHeap_self` (hypothesis 3): necessary, empty state, v = none: initHeap inserts cell 0
theorem w6c4_4 : ¬ drop0% Iris.HeapLang.State.initHeap_self 3 := fun h => by
  have := congrArg (fun s : HeapLang.State => PartialMap.get? (M := HeapF) s.heap ⟨0⟩) (h (σ := ⟨∅, ∅⟩) (l := ⟨0⟩) (v := none))
  simp [Std.LawfulPartialMap.get?_insert, Std.LawfulPartialMap.get?_empty] at this

-- `Iris.HeapLang.alloc_fresh` (hypothesis 3): necessary, n = 0: no allocation step of size 0
theorem w6c4_5 : ¬ drop0% Iris.HeapLang.alloc_fresh 3 := fun h => by
  have := h (.lit .unit) 0 default
  cases this
  omega

-- `Iris.Instances.Data.disjoint_assoc` (hypothesis 4): necessary, a = c = everywhere result (), b empty
theorem w6c4_6 : ¬ drop0% Iris.Instances.Data.disjoint_assoc 4 := fun h => by
  have := (@h Unit (fun _ => .result ()) (fun _ => .unknown) (fun _ => .result ()) (fun _ => .inr rfl)).1 0
  rcases this with h | h <;> cases h

-- `Iris.Instances.Data.disjoint_assoc` (hypothesis 5): removable, a ∪ b is unknown only where a and b both are
theorem w6c4_7 : drop% Iris.Instances.Data.disjoint_assoc 5 := by
  intro Val a b c h
  refine ⟨fun i => ?_, fun i => ?_⟩ <;>
  · have hi : _ ∨ _ := h i
    simp only [Union.union] at hi
    rcases ha : a i <;> rcases hb : b i <;> simp [ha, hb] at hi ⊢ <;> assumption

-- `Iris.Instances.Data.disjoint_union` (hypothesis 4): necessary, a = b = everywhere result (), c empty
theorem w6c4_8 : ¬ drop0% Iris.Instances.Data.disjoint_union 4 := fun h => by
  have := (@h Unit (fun _ => .result ()) (fun _ => .result ()) (fun _ => .unknown) (fun _ => .inr rfl)) 0
  rcases this with h | h <;> cases h

-- `Iris.Instances.Data.disjoint_union` (hypothesis 5): necessary, a = c = everywhere result (), b empty
theorem w6c4_9 : ¬ drop0% Iris.Instances.Data.disjoint_union 5 := fun h => by
  have := (@h Unit (fun _ => .result ()) (fun _ => .unknown) (fun _ => .result ()) (fun _ => .inr rfl)) 0
  rcases this with h | h <;> cases h

end

open Iris Iris.BI COFE W6c4

-- `Iris.IProp.unfoldi_validN` (hypothesis 4): necessary, GFc slot 0, x = error
theorem w6c4_20 : ¬ drop0% Iris.IProp.unfoldi_validN 4 := fun h =>
  cr_inv (h (FF := GFc) (τ := 0) (n := 0) cr)

-- `Iris.IProp.validN_foldi` (hypothesis 4): necessary, GFc slot 0, x = error
theorem w6c4_21 : ¬ drop0% Iris.IProp.validN_foldi 4 := fun h =>
  cr_inv (h (FF := GFc) (τ := 0) (n := 0) cr)

-- `Iris.ElemG.bundle_validN` (hypothesis 6): necessary, GFc, a = error
theorem w6c4_22 : ¬ drop0% Iris.ElemG.bundle_validN 6 := fun h =>
  cr_inv (h (GF := GFc) (F := constOF CoPsetDisjL) (n := 0) (a := cr))

-- `Iris.ElemG.unbundle_validN` (hypothesis 6): necessary, GFc, a = error
theorem w6c4_23 : ¬ drop0% Iris.ElemG.unbundle_validN 6 := fun h =>
  cr_inv (h (GF := GFc) (F := constOF CoPsetDisjL) (n := 0) (a := cr))

-- `Iris.IProp.unfoldi_bundle_validN` (hypothesis 6): necessary, GFc, a = error
theorem w6c4_24 : ¬ drop0% Iris.IProp.unfoldi_bundle_validN 6 := fun h =>
  cr_inv (h (GF := GFc) (F := constOF CoPsetDisjL) (n := 0) (a := cr))

-- `Iris.validN_of_iSingleton` (hypothesis 7): necessary, GFc, a = error
theorem w6c4_25 : ¬ drop0% Iris.validN_of_iSingleton 7 := fun h =>
  cr_inv (h (GF := GFc) (F := constOF CoPsetDisjL) (n := 0) (γ := 0) (a := cr))

-- `Iris.iSingleton_validN_at_E_τ` (hypothesis 7): necessary, GFc, a = error is stored at γ
theorem w6c4_26 : ¬ drop0% Iris.iSingleton_validN_at_E_τ 7 := fun h => by
  have := h (GF := GFc) (F := constOF CoPsetDisjL) (n := 0) (γ := 0) (a := cr) 0
  rw [sg_at] at this
  exact cr_inv (n := 0) this

-- `Iris.iSingleton_validN_at_ne` (hypothesis 8): necessary, GFc, τ' = E.τ, a = error
theorem w6c4_27 : ¬ drop0% Iris.iSingleton_validN_at_ne 8 := fun h => by
  have := h (GF := GFc) (F := constOF CoPsetDisjL) (n := 0) (γ := 0) (a := cr) (τ' := ElemG.τ GFc (constOF CoPsetDisjL)) 0
  rw [sg_at] at this
  exact cr_inv (n := 0) this

-- `Iris.validN_bundle_op_foldi` (hypothesis 7): necessary, GFc, a' = error (error absorbs)
theorem w6c4_28 : ¬ drop0% Iris.validN_bundle_op_foldi 7 := fun h =>
  cr_inv (h (GF := GFc) (F := constOF CoPsetDisjL) (n := 0) (a' := cr) (v := ce))

-- `Iris.iSingleton_free_at_ne` (hypothesis 7): necessary, GFc, γ' = γ
theorem w6c4_29 : ¬ drop0% Iris.iSingleton_free_at_ne 7 := fun h => by
  have := h (GF := GFc) (F := constOF CoPsetDisjL) (γ := 0) (v := ce) (γ' := 0)
  rw [sg_at] at this
  cases this

-- `Iris.iSingleton_ne_eq_unit` (hypothesis 7): necessary, GFc, τ' = E.τ
theorem w6c4_30 : ¬ drop0% Iris.iSingleton_ne_eq_unit 7 := fun h => by
  have := congrFun (h (GF := GFc) (F := constOF CoPsetDisjL) (γ := 0) (v := ce) (τ' := ElemG.τ GFc (constOF CoPsetDisjL))) 0
  rw [sg_at] at this
  cases this

-- `Iris.extract_frame_validN` (hypothesis 7): necessary, GFc, mz' = unit, v = error
theorem w6c4_31 : ¬ drop0% Iris.extract_frame_validN 7 := fun h =>
  cr_inv (h (GF := GFc) (τ := 0) (n := 0) (mz' := UORA.unit) (fun _ => trivial) (γ := 0) (v := cr))

-- `Iris.extract_frame_validN` (hypothesis 4): necessary, GFc, mz' = singleton 0 error
theorem w6c4_32 : ¬ drop0% Iris.extract_frame_validN 4 := fun h =>
  cr_inv (h (GF := GFc) (τ := 0) (n := 0) (mz' := iSingleton (GF := GFc) (constOF CoPsetDisjL) 0 cr) (γ := 0) (v := cr) (sg_at 0 cr))

-- `Iris.iSingleton_op_ne_free` (hypothesis 8): necessary, GFc, γ' = γ = 0, m empty: the singleton entry remains
theorem w6c4_33 : ¬ drop0% Iris.iSingleton_op_ne_free 8 := fun h => by
  have := h (GF := GFc) (F := constOF CoPsetDisjL) (γ := 0) (v := ce) (m := GenMap.empty) (γ' := 0) rfl
  change (some ce : Option CoPsetDisjL) • none = none at this
  rw [show ((some ce : Option CoPsetDisjL) • none) = some ce from rfl] at this
  cases this

-- `Iris.iSingleton_op_ne_free` (hypothesis 9): necessary, GFc, γ = 0, γ' = 1, m has an entry at 1
theorem w6c4_34 : ¬ drop0% Iris.iSingleton_op_ne_free 9 := fun h => by
  have := h (GF := GFc) (F := constOF CoPsetDisjL) (γ := 0) (v := ce) (m := GenMap.singleton 1 ce) (γ' := 1) (by decide)
  change (none : Option CoPsetDisjL) • some ce = none at this
  rw [show ((none : Option CoPsetDisjL) • some ce) = some ce from rfl] at this
  cases this

-- `Iris.iSingleton_op_alter` (hypothesis 7): necessary, GFc, r = unit, v = valid ∅: the left side has an entry at γ
theorem w6c4_35 : ¬ drop0% Iris.iSingleton_op_alter 7 := fun h => by
  have := congrArg (fun r : IResUR GFc => (r (ElemG.τ GFc (constOF CoPsetDisjL))).car 0)
    (h (GF := GFc) (F := constOF CoPsetDisjL) (γ := 0) (r := UORA.unit) (v := ce))
  change (some ce : Option CoPsetDisjL) • none = none at this
  rw [show ((some ce : Option CoPsetDisjL) • none) = some ce from rfl] at this
  cases this

-- `Iris.validN_of_iSingleton_op_free` (hypothesis 8): necessary, GFc, mf = unit, y = error
theorem w6c4_36 : ¬ drop0% Iris.validN_of_iSingleton_op_free 8 := fun h =>
  cr_inv (h (GF := GFc) (F := constOF CoPsetDisjL) (n := 0) (γ := 0) (mf := UORA.unit) (y := cr) rfl)

-- `Iris.validN_of_iSingleton_op_free` (hypothesis 9): removable, validity of a product implies validity of the left factor
theorem w6c4_37 : drop% Iris.validN_of_iSingleton_op_free 9 := by
  intro GF F _ E n γ mf y Hv
  exact validN_of_iSingleton (ORA.validN_op_left Hv)

-- `Iris.validN_mf_at_E_τ_of_iSingleton_op_free` (hypothesis 8): necessary, GFc, mf = error at name 1, γ = 0
theorem w6c4_38 : ¬ drop0% Iris.validN_mf_at_E_τ_of_iSingleton_op_free 8 := fun h => by
  have := h (GF := GFc) (F := constOF CoPsetDisjL) (n := 0) (γ := 0) (mf := sgc 1 cr) (y := ce) (sg_ne cr (by decide)) 1
  rw [sg_at] at this
  exact cr_inv (n := 0) this

-- `Iris.validN_mf_at_E_τ_of_iSingleton_op_free` (hypothesis 9): removable, validity of a product implies validity of the right factor
theorem w6c4_39 : drop% Iris.validN_mf_at_E_τ_of_iSingleton_op_free 9 := by
  intro GF F _ E n γ mf y Hv
  exact ORA.validN_op_right Hv (ElemG.τ GF F)

-- `Iris.validN_mf_at_ne_of_iSingleton_op` (hypothesis 8): necessary, GFc, mf = error at name 0 in every slot, τ' = 1
theorem w6c4_40 : ¬ drop0% Iris.validN_mf_at_ne_of_iSingleton_op 8 := fun h => by
  have := h (GF := GFc) (F := constOF CoPsetDisjL) (n := 0) (γ := 0) (mf := allBad) (y := ce) (τ' := 1) (by decide) 0
  change ✓{0} (some cr) at this
  exact cr_inv (n := 0) this

-- `Iris.validN_mf_at_ne_of_iSingleton_op` (hypothesis 10): removable, validity of a product implies validity of the right factor
theorem w6c4_41 : drop% Iris.validN_mf_at_ne_of_iSingleton_op 10 := by
  intro GF F _ E n γ mf y Hv τ'
  exact ORA.validN_op_right Hv τ'

-- `Iris.iSingleton_op_validN_free` (hypothesis 8): necessary, GFc, mf = unit, y = error
theorem w6c4_42 : ¬ drop0% Iris.iSingleton_op_validN_free 8 := fun h =>
  cr_inv (h (GF := GFc) (F := constOF CoPsetDisjL) (n := 0) (γ := 0) (mf := UORA.unit) (y := cr) rfl).1

-- `Iris.iSingleton_op_validN_free` (hypothesis 9): removable, both factors of a valid product are valid
theorem w6c4_43 : drop% Iris.iSingleton_op_validN_free 9 := by
  intro GF F _ E n γ mf y Hv
  exact ⟨validN_of_iSingleton (ORA.validN_op_left Hv), ORA.validN_op_right Hv⟩

-- `Iris.iSingleton_op_validN_notfree` (hypothesis 9): necessary, GFc, mf = singleton 0 (valid ∅), y = error
theorem w6c4_44 : ¬ drop0% Iris.iSingleton_op_validN_notfree 9 := fun h =>
  cr_inv (h (GF := GFc) (F := constOF CoPsetDisjL) (n := 0) (γ := 0) (v := ce) (mf := sgc 0 ce) (y := cr) (sg_at 0 ce))

-- `Iris.iSingleton_op_validN_notfree` (hypothesis 10): necessary, GFc, mf = unit, y = valid ∅, v = error
theorem w6c4_45 : ¬ drop0% Iris.iSingleton_op_validN_notfree 10 := fun h =>
  cr_inv (h (GF := GFc) (F := constOF CoPsetDisjL) (n := 0) (γ := 0) (v := cr) (mf := UORA.unit) (y := ce)
    (validN_iSingleton_op UORA.unit_valid.validN DisjointLeibnizSet.validN_set rfl))

-- `Iris.validN_iSingleton_op` (hypothesis 8): necessary, GFc, γ = 1, mf = error at name 0 in every slot
theorem w6c4_46 : ¬ drop0% Iris.validN_iSingleton_op 8 := fun h => by
  have := h (GF := GFc) (F := constOF CoPsetDisjL) (n := 0) (γ := 1) (mf := allBad) (y := ce) DisjointLeibnizSet.validN_set rfl 0 0
  change ✓{0} ((none : Option CoPsetDisjL) • some cr) at this
  exact cr_inv (n := 0) this

-- `Iris.validN_iSingleton_op` (hypothesis 9): necessary, GFc, mf = unit, y = error
theorem w6c4_47 : ¬ drop0% Iris.validN_iSingleton_op 9 := fun h => by
  have := h (GF := GFc) (F := constOF CoPsetDisjL) (n := 0) (γ := 0) (mf := UORA.unit) (y := cr) UORA.unit_valid.validN rfl 0 0
  change ✓{0} ((some cr : Option CoPsetDisjL) • none) at this
  exact cr_inv (n := 0) this

-- `Iris.validN_iSingleton_op` (hypothesis 10): necessary, GFc, mf = singleton 0 (valid ⊤), y = valid ⊤: ⊤ is not disjoint from itself
theorem w6c4_48 : ¬ drop0% Iris.validN_iSingleton_op 10 := fun h => by
  have := h (GF := GFc) (F := constOF CoPsetDisjL) (n := 0) (γ := 0) (mf := sgc 0 (.valid CoPset.full)) (y := .valid CoPset.full)
    (s_valid DisjointLeibnizSet.validN_set) DisjointLeibnizSet.validN_set 0 0
  change ✓{0} ((DisjointLeibnizSet.valid CoPset.full : CoPsetDisjL) • DisjointLeibnizSet.valid CoPset.full) at this
  change ✓{0} (if CoPset.full ## CoPset.full then _ else _) at this
  rw [if_neg full_not_disj] at this
  exact this

-- `Iris.iSingleton_op_validN_at_E` (hypothesis 9): necessary, GFc, mf = unit, a = error
theorem w6c4_49 : ¬ drop0% Iris.iSingleton_op_validN_at_E 9 := fun h => by
  have := h (GF := GFc) (F := constOF CoPsetDisjL) (n := 0) (mf := UORA.unit) (γ := 0) (a := cr) UORA.unit_valid.validN 0 0
  change ✓{0} ((some cr : Option CoPsetDisjL) • none) at this
  exact cr_inv (n := 0) this

-- `Iris.iSingleton_op_validN_at_γ` (hypothesis 9): necessary, GFc, mf = unit, a = error
theorem w6c4_50 : ¬ drop0% Iris.iSingleton_op_validN_at_γ 9 := fun h => by
  have := h (GF := GFc) (F := constOF CoPsetDisjL) (n := 0) (mf := UORA.unit) (γ := 0) (a := cr) UORA.unit_valid.validN 0 0
  change ✓{0} ((some cr : Option CoPsetDisjL) • none) at this
  exact cr_inv (n := 0) this

-- `Iris.validN_iSingleton_op_notfree` (hypothesis 12): necessary, GFc, a = v = valid ∅, mz' = singleton 0 (valid ∅), a' = error
theorem w6c4_51 : ¬ drop0% Iris.validN_iSingleton_op_notfree 12 := fun h => by
  have := h (GF := GFc) (F := constOF CoPsetDisjL) (n := 0) (γ := 0) (a := ce) (v := ce) (a' := cr) (mz' := sgc 0 ce)
    (by rw [iSingleton_op]; exact s_valid ce_ce_valid) (sg_at 0 ce) 0
  change ✓{0} ((some cr : Option CoPsetDisjL) • some ce) at this
  exact cr_inv (n := 0) this

-- `Iris.validN_iSingleton_op_notfree` (hypothesis 11): necessary, GFc, a = v = valid ∅, mz' = singleton 0 (valid ⊤), a' = valid ⊤
theorem w6c4_52 : ¬ drop0% Iris.validN_iSingleton_op_notfree 11 := fun h => by
  have := h (GF := GFc) (F := constOF CoPsetDisjL) (n := 0) (γ := 0) (a := ce) (v := ce) (a' := .valid CoPset.full)
    (mz' := sgc 0 (.valid CoPset.full))
    (by
      rw [iSingleton_op]; refine s_valid ?_
      change ✓{0} (if (∅ : CoPset) ## CoPset.full then _ else _)
      rw [if_pos (show (∅ : CoPset) ## CoPset.full from fun _ ⟨h, _⟩ => CoPset.mem_empty h)]; trivial)
    (by
      change ✓{0} (if CoPset.full ## ∅ then _ else _)
      rw [if_pos (disj_empty _)]; trivial) 0
  change ✓{0} ((DisjointLeibnizSet.valid CoPset.full : CoPsetDisjL) • DisjointLeibnizSet.valid CoPset.full) at this
  change ✓{0} (if CoPset.full ## CoPset.full then _ else _) at this
  rw [if_neg full_not_disj] at this
  exact this

-- `Iris.alloc_update_unit` (hypothesis 5): necessary, GFc, f = constant error: the updated singleton is invalid
theorem w6c4_53 : ¬ drop0% Iris.alloc_update_unit 5 := fun h => by
  obtain ⟨y, ⟨γ, rfl⟩, hv⟩ := h (GF := GFc) (F := constOF CoPsetDisjL) (f := fun _ => cr) 0 none UORA.unit_valid.validN
  exact cr_inv (validN_of_iSingleton (n := 0) hv)

-- `Iris.singleton_updateP` (hypothesis 7): necessary, GFc, P = False, a = valid ∅
theorem w6c4_54 : ¬ drop0% Iris.singleton_updateP 7 := fun h => by
  obtain ⟨y, ⟨a', _, hf⟩, _⟩ := h (GF := GFc) (F := constOF CoPsetDisjL) (P := fun _ => False) (γ := 0) (a := ce) 0 none
    (s_valid (n := 0) DisjointLeibnizSet.validN_set)
  exact hf

-- `Iris.iOwn_alloc_dep` (hypothesis 5): necessary, GFc, f = constant error
theorem w6c4_55 : ¬ drop0% Iris.iOwn_alloc_dep 5 := fun h => bupd_false_unsound
  ((h (GF := GFc) (F := constOF CoPsetDisjL) (fun _ => cr)).trans (BIUpdate.mono (BI.exists_elim fun γ => own_cr_false γ)))

-- `Iris.iOwn_alloc` (hypothesis 5): necessary, GFc, a = error
theorem w6c4_56 : ¬ drop0% Iris.iOwn_alloc 5 := fun h => bupd_false_unsound
  ((h (GF := GFc) (F := constOF CoPsetDisjL) cr).trans (BIUpdate.mono (BI.exists_elim fun γ => own_cr_false γ)))

-- `Iris.iOwn_alloc_strong_dep` (hypothesis 7): necessary, GFc, P = True, f = constant error
theorem w6c4_57 : ¬ drop0% Iris.iOwn_alloc_strong_dep 7 := fun h => bupd_false_unsound
  ((h (GF := GFc) (F := constOF CoPsetDisjL) (fun _ => cr) (fun _ => True) (fun N => ⟨N, Nat.le_refl N, trivial⟩)).trans
    (BIUpdate.mono (BI.exists_elim fun γ => BI.sep_elim_right.trans (own_cr_false γ))))

-- `Iris.iOwn_alloc_cofinite_dep` (hypothesis 6): necessary, GFc, G = [], f = constant error
theorem w6c4_58 : ¬ drop0% Iris.iOwn_alloc_cofinite_dep 6 := fun h => bupd_false_unsound
  ((h (GF := GFc) (F := constOF CoPsetDisjL) (fun _ => cr) []).trans
    (BIUpdate.mono (BI.exists_elim fun γ => BI.sep_elim_right.trans (own_cr_false γ))))

-- `Iris.iOwn_alloc_strong` (hypothesis 7): necessary, GFc, P = True, a = error
theorem w6c4_59 : ¬ drop0% Iris.iOwn_alloc_strong 7 := fun h => bupd_false_unsound
  ((h (GF := GFc) (F := constOF CoPsetDisjL) cr (fun _ => True) (fun N => ⟨N, Nat.le_refl N, trivial⟩)).trans
    (BIUpdate.mono (BI.exists_elim fun γ => BI.sep_elim_right.trans (own_cr_false γ))))

-- `Iris.iOwn_alloc_cofinite` (hypothesis 6): necessary, GFc, G = [], a = error
theorem w6c4_60 : ¬ drop0% Iris.iOwn_alloc_cofinite 6 := fun h => bupd_false_unsound
  ((h (GF := GFc) (F := constOF CoPsetDisjL) cr []).trans
    (BIUpdate.mono (BI.exists_elim fun γ => BI.sep_elim_right.trans (own_cr_false γ))))

-- `Iris.iOwn_mono` (hypothesis 7): necessary, GFc, a1 = valid ∅ (allocatable), a2 = error
theorem w6c4_61 : ¬ drop0% Iris.iOwn_mono 7 := fun h => bupd_false_unsound
  (alloc_ce.trans (BIUpdate.mono (BI.exists_elim fun γ =>
    (h (GF := GFc) (F := constOF CoPsetDisjL) (γ := γ) (a1 := ce) (a2 := cr)).trans (own_cr_false γ))))

-- `Iris.iOwn_update` (hypothesis 7): necessary, GFc, a = valid ∅, a' = error
theorem w6c4_62 : ¬ drop0% Iris.iOwn_update 7 := fun h => bupd_false_unsound
  (alloc_ce.trans ((BIUpdate.mono (BI.exists_elim fun γ =>
    (h (GF := GFc) (F := constOF CoPsetDisjL) (γ := γ) (a := ce) (a' := cr)).trans
      (BIUpdate.mono (own_cr_false γ)))).trans BIUpdate.trans))

-- `Iris.iOwn_updateP` (hypothesis 7): necessary, GFc, P = False, a = valid ∅
theorem w6c4_63 : ¬ drop0% Iris.iOwn_updateP 7 := fun h => bupd_false_unsound
  (alloc_ce.trans ((BIUpdate.mono (BI.exists_elim fun γ =>
    (h (GF := GFc) (F := constOF CoPsetDisjL) (P := fun _ => False) (γ := γ) (a := ce)).trans
      (BIUpdate.mono (BI.exists_elim fun _ => BI.sep_elim_left)))).trans BIUpdate.trans))

-- `Iris.iOwn_update_op` (hypothesis 8): necessary, GFc, a1 = a2 = valid ∅ (own of ce • ce splits), a' = error
theorem w6c4_64 : ¬ drop0% Iris.iOwn_update_op 8 := fun h => bupd_false_unsound
  ((iOwn_alloc (GF := GFc) (F := constOF CoPsetDisjL) (ce • ce) (ORA.valid_iff_validN.mpr fun _ => ce_ce_valid)).trans
    ((BIUpdate.mono (BI.exists_elim fun γ => (iOwn_op (GF := GFc) (F := constOF CoPsetDisjL) (γ := γ) (a1 := ce) (a2 := ce)).mp.trans
    ((h (GF := GFc) (F := constOF CoPsetDisjL) (γ := γ) (a1 := ce) (a2 := ce) (a' := cr)).trans
      (BIUpdate.mono (own_cr_false γ))))).trans BIUpdate.trans))

-- `Iris.iOwn_update_op_op` (hypothesis 9): necessary, GFc, a1 = a2 = a3 = valid ∅ (own of (ce • ce) • ce splits), a' = error
theorem w6c4_65 : ¬ drop0% Iris.iOwn_update_op_op 9 := fun h => bupd_false_unsound
  (alloc_3.trans ((BIUpdate.mono (BI.exists_elim fun γ =>
    (h (GF := GFc) (F := constOF CoPsetDisjL) (γ := γ) (a1 := ce) (a2 := ce) (a3 := ce) (a' := cr)).trans
      (BIUpdate.mono (own_cr_false γ)))).trans BIUpdate.trans))

-- `Iris.intoSep_own` (hypothesis 8): necessary, GFc, a = valid ∅, b1 = b2 = error
theorem w6c4_66 : ¬ drop0% Iris.intoSep_own 8 := fun h => bupd_false_unsound
  (alloc_ce.trans (BIUpdate.mono (BI.exists_elim fun γ =>
    (h (GF := GFc) (F := constOF CoPsetDisjL) (b1 := cr) (b2 := cr) (γ := γ) (a := ce)).into_sep.trans
      (BI.sep_elim_left.trans (own_cr_false γ)))))

-- `Iris.intoAnd_own` (hypothesis 8): necessary, GFc, a = valid ∅, b1 = b2 = error
theorem w6c4_67 : ¬ drop0% Iris.intoAnd_own 8 := fun h => bupd_false_unsound
  (alloc_ce.trans (BIUpdate.mono (BI.exists_elim fun γ =>
    (h (GF := GFc) (F := constOF CoPsetDisjL) (γ := γ) (a := ce) (b1 := cr) (b2 := cr)).into_and.trans
      (BI.and_elim_l.trans (own_cr_false γ)))))

-- `Iris.fromSep_own` (hypothesis 8): necessary, GFc, b1 = b2 = valid ∅, a = error
theorem w6c4_68 : ¬ drop0% Iris.fromSep_own 8 := fun h => bupd_false_unsound
  (alloc_2.trans (BIUpdate.mono (BI.exists_elim fun γ =>
    (h (GF := GFc) (F := constOF CoPsetDisjL) (γ := γ) (a := cr) (b1 := ce) (b2 := ce)).from_sep.trans (own_cr_false γ))))

-- `Iris.combineSepAs_iOwn` (hypothesis 8): necessary, GFc, b1 = b2 = valid ∅, a = error
theorem w6c4_69 : ¬ drop0% Iris.combineSepAs_iOwn 8 := fun h => bupd_false_unsound
  (alloc_2.trans (BIUpdate.mono (BI.exists_elim fun γ =>
    (h (GF := GFc) (F := constOF CoPsetDisjL) (γ := γ) (a := cr) (b1 := ce) (b2 := ce)).combine_sep_as.trans (own_cr_false γ))))

-- `Iris.fromAndOwn_persistent` (hypothesis 8): necessary, GFc, b1 = b2 = valid ∅ (a core id), a = error
theorem w6c4_70 : ¬ drop0% Iris.fromAndOwn_persistent 8 := fun h => bupd_false_unsound
  (alloc_ce.trans (BIUpdate.mono (BI.exists_elim fun γ =>
    (BI.and_intro .rfl .rfl).trans
    ((h (GF := GFc) (F := constOF CoPsetDisjL) (γ := γ) (a := cr) (b1 := ce) (b2 := ce)).from_and.trans (own_cr_false γ)))))

-- `Iris.iResProject_below` (hypothesis 7): necessary, GFc, z = unit, c = valid ∅: unit has no entry at γ
theorem w6c4_71 : ¬ drop0% Iris.iResProject_below 7 := fun h => by
  obtain ⟨w, e⟩ := h (GF := GFc) (F := constOF CoPsetDisjL) (γ := 0) (z := UORA.unit) (c := ce)
  have := congrArg (fun r : IResUR GFc => (r 0).car 0) e
  change (none : Option CoPsetDisjL) = (some ce • (w 0).car 0) at this
  rcases hw : (w 0).car 0 with _ | b <;> rw [hw] at this <;> cases this

-- `Iris.iResProject_ord_monoN` (hypothesis 8): necessary, GFc, x = singleton 0 (valid ∅), y = unit
theorem w6c4_72 : ¬ drop0% Iris.iResProject_ord_monoN 8 := fun h => by
  have := h (GF := GFc) (F := constOF CoPsetDisjL) (γ := 0) (n := 0) (x := sgc 0 ce) (y := UORA.unit)
  change (some ce : Option CoPsetDisjL) ≼ₒ{0} (none : Option CoPsetDisjL) at this
  exact Option.not_some_ordN_none this

-- `Iris.iResProject_none_incl_false` (hypothesis 7): necessary, GFc, z = singleton γ a itself
theorem w6c4_73 : ¬ drop0% Iris.iResProject_none_incl_false 7 := fun h =>
  pure_soundness (PROP := IProp GFc)
    ((internalCmraIncluded_intro (P := iprop(emp)) (ORA.inc_refl (sgc 0 ce))).trans
      (h (GF := GFc) (F := constOF CoPsetDisjL) (γ := 0) (z := sgc 0 ce) ce))

-- `Iris.iResProject_none_ord_false` (hypothesis 7): necessary, GFc, z = singleton γ a itself
theorem w6c4_74 : ¬ drop0% Iris.iResProject_none_ord_false 7 := fun h =>
  pure_soundness (PROP := IProp GFc)
    (internalCmraOrder_refl.trans (h (GF := GFc) (F := constOF CoPsetDisjL) (γ := 0) (z := sgc 0 ce) ce))

-- `Iris.iOwn_ord_and_discrete_total` (hypothesis 10): necessary, GFc, a1 = a2 = valid ∅, c = error
theorem w6c4_75 : ¬ drop0% Iris.iOwn_ord_and_discrete_total 10 := fun h => bupd_false_unsound
  (alloc_ce.trans (BIUpdate.mono (BI.exists_elim fun γ => (BI.and_intro .rfl .rfl).trans
    ((h (GF := GFc) (F := constOF CoPsetDisjL) (γ := γ) (a1 := ce) (a2 := ce) (c := cr)).trans (own_cr_false γ)))))

-- `Iris.iOwn_ord_and_discrete_total_false` (hypothesis 9): necessary, GFc, a1 = a2 = valid ∅
theorem w6c4_76 : ¬ drop0% Iris.iOwn_ord_and_discrete_total_false 9 := fun h => bupd_false_unsound
  (alloc_ce.trans (BIUpdate.mono (BI.exists_elim fun γ => (BI.and_intro .rfl .rfl).trans
    (h (GF := GFc) (F := constOF CoPsetDisjL) (γ := γ) (a1 := ce) (a2 := ce)))))

-- `Iris.iOwn_and_discrete_total` (hypothesis 11): necessary, GFc, a1 = a2 = valid ∅, c = error
theorem w6c4_77 : ¬ drop0% Iris.iOwn_and_discrete_total 11 := fun h => bupd_false_unsound
  (alloc_ce.trans (BIUpdate.mono (BI.exists_elim fun γ => (BI.and_intro .rfl .rfl).trans
    ((h (GF := GFc) (F := constOF CoPsetDisjL) (γ := γ) (a1 := ce) (a2 := ce) (c := cr)).trans (own_cr_false γ)))))

-- `Iris.iOwn_and_discrete_total_false` (hypothesis 10): necessary, GFc, a1 = a2 = valid ∅
theorem w6c4_78 : ¬ drop0% Iris.iOwn_and_discrete_total_false 10 := fun h => bupd_false_unsound
  (alloc_ce.trans (BIUpdate.mono (BI.exists_elim fun γ => (BI.and_intro .rfl .rfl).trans
    (h (GF := GFc) (F := constOF CoPsetDisjL) (γ := γ) (a1 := ce) (a2 := ce)))))

-- `Iris.IProp.unfoldi_unit` (hypothesis 3): necessary, GFc, x = error is not a unit (not valid)
theorem w6c4_79 : ¬ drop0% Iris.IProp.unfoldi_unit 3 := fun h =>
  cr_inv (ORA.valid_iff_validN.mp (h (FF := GFc) (τ := 0) (x := cr)).unit_valid 0)

-- `Iris.ElemG.bundle_unit` (hypothesis 5): necessary, GFc, ε = error is not a unit (not valid)
theorem w6c4_80 : ¬ drop0% Iris.ElemG.bundle_unit 5 := fun h =>
  cr_inv (ORA.valid_iff_validN.mp (h (E := elemC) (ε := cr)).unit_valid 0)

-- `Iris.IProp.unfoldi_bundle_unit` (hypothesis 5): necessary, GFc, ε = error is not a unit (not valid)
theorem w6c4_81 : ¬ drop0% Iris.IProp.unfoldi_bundle_unit 5 := fun h =>
  cr_inv (ORA.valid_iff_validN.mp (h (GF := GFc) (F := constOF CoPsetDisjL) (ε := cr)).unit_valid 0)

-- `Iris.iSingleton_op_validN_at_E` (hypothesis 8): necessary, GFc, mf empty in slot 0, error at name 0 in the other slots
theorem w6c4_82 : ¬ drop0% Iris.iSingleton_op_validN_at_E 8 := fun h => by
  have := h (GF := GFc) (F := constOF CoPsetDisjL) (n := 0) (mf := mf1) (γ := 0) (a := ce)
    ((validN_iSingleton_op (GF := GFc) (F := constOF CoPsetDisjL) (mf := UORA.unit) (γ := 0) (y := ce)
      UORA.unit_valid.validN DisjointLeibnizSet.validN_set rfl) (ElemG.τ GFc (constOF CoPsetDisjL))) 1 0
  change ✓{0} ((none : Option CoPsetDisjL) • some cr) at this
  exact cr_inv (n := 0) this

-- `Iris.iSingleton_op_validN_at_γ` (hypothesis 8): necessary, GFc, mf empty in slot 0, error at name 0 in the other slots
theorem w6c4_83 : ¬ drop0% Iris.iSingleton_op_validN_at_γ 8 := fun h => by
  have := h (GF := GFc) (F := constOF CoPsetDisjL) (n := 0) (mf := mf1) (γ := 0) (a := ce)
    (show ✓{0} ((some ce : Option CoPsetDisjL) • none) from (show ✓{0} ce from DisjointLeibnizSet.validN_set)) 1 0
  change ✓{0} ((none : Option CoPsetDisjL) • some cr) at this
  exact cr_inv (n := 0) this

-- `Iris.iOwn_ord_forall_total` (hypothesis 4): necessary, XB (no OrderRefl): B = Unit, f = true; nothing valid is above true
theorem w6c4_84 : ¬ drop0% Iris.iOwn_ord_forall_total 4 := fun h => bupd_false_unsound
  (alloc_xt.trans (BIUpdate.mono (BI.exists_elim fun γ => (BI.forall_intro fun _ : Unit => .rfl).trans
    ((h (GF := GFx) (F := constOF XB) (B := Unit) γ (fun _ => xt)).trans
      (BI.exists_elim fun c => (BI.sep_mono (own_x γ c) ((BI.forall_elim ()).trans (xo c))).trans xbad)))))

-- `Iris.iOwn_ord_and_total` (hypothesis 5): necessary, XB (no OrderRefl): a1 = a2 = true
theorem w6c4_85 : ¬ drop0% Iris.iOwn_ord_and_total 5 := fun h => bupd_false_unsound
  (alloc_xt.trans (BIUpdate.mono (BI.exists_elim fun γ => (BI.and_intro .rfl .rfl).trans
    ((h (GF := GFx) (F := constOF XB) (γ := γ) (a1 := xt) (a2 := xt)).trans
      (BI.exists_elim fun c => (BI.sep_mono (own_x γ c) (BI.sep_elim_left.trans (xo c))).trans xbad)))))

-- `Iris.iOwn_ord_forall_pred_total` (hypothesis 4): necessary, XB (no OrderRefl): B = Unit, φ = True, f = true
theorem w6c4_86 : ¬ drop0% Iris.iOwn_ord_forall_pred_total 4 := fun h => bupd_false_unsound
  (alloc_xt.trans (BIUpdate.mono (BI.exists_elim fun γ =>
    (BI.forall_intro fun _ : Unit => BI.wand_intro BI.sep_elim_left).trans
    ((@h GFx (constOF XB) _ elemX Unit γ (fun _ => True) ⟨⟨(), trivial⟩⟩ (fun _ => xt)).trans
      (BI.exists_elim fun c => (BI.sep_mono (own_x γ c)
        ((BI.forall_elim ()).trans (BI.sep_emp.mpr.trans ((BI.sep_mono_right (BI.pure_intro trivial)).trans
          (BI.wand_elim_left.trans (xo c)))))).trans xbad)))))

-- `Iris.iOwn_ord_and_discrete_total` (hypothesis 6): necessary, XB (no OrderRefl): a1 = a2 = true, c = false; h holds vacuously
theorem w6c4_87 : ¬ drop0% Iris.iOwn_ord_and_discrete_total 6 := fun h => bupd_false_unsound
  (alloc_xt.trans (BIUpdate.mono (BI.exists_elim fun γ => (BI.and_intro .rfl .rfl).trans
    ((h (GF := GFx) (F := constOF XB) (γ := γ) (a1 := xt) (a2 := xt) (c := xf)
      (fun c' hv h1 _ => (xb_no_up c' hv h1).elim)).trans (own_xf_false γ)))))

-- `Iris.iOwn_ord_and_discrete_total_false` (hypothesis 6): necessary, XB (no OrderRefl): a1 = a2 = true; h holds vacuously
theorem w6c4_88 : ¬ drop0% Iris.iOwn_ord_and_discrete_total_false 6 := fun h => bupd_false_unsound
  (alloc_xt.trans (BIUpdate.mono (BI.exists_elim fun γ => (BI.and_intro .rfl .rfl).trans
    (h (GF := GFx) (F := constOF XB) (γ := γ) (a1 := xt) (a2 := xt) (fun c' hv h1 _ => xb_no_up c' hv h1)))))

-- `Iris.iOwn_forall_total` (hypothesis 5): necessary, XB (OrdInc, not IsTotal): B = Unit, f = true
theorem w6c4_89 : ¬ drop0% Iris.iOwn_forall_total 5 := fun h => bupd_false_unsound
  (alloc_xt.trans (BIUpdate.mono (BI.exists_elim fun γ => (BI.forall_intro fun _ : Unit => .rfl).trans
    ((h (GF := GFx) (F := constOF XB) (B := Unit) γ (fun _ => xt)).trans
      (BI.exists_elim fun c => (BI.sep_mono (own_x γ c) ((BI.forall_elim ()).trans (xi c))).trans xbad)))))

-- `Iris.iOwn_and_total` (hypothesis 6): necessary, XB (OrdInc, not IsTotal): a1 = a2 = true
theorem w6c4_90 : ¬ drop0% Iris.iOwn_and_total 6 := fun h => bupd_false_unsound
  (alloc_xt.trans (BIUpdate.mono (BI.exists_elim fun γ => (BI.and_intro .rfl .rfl).trans
    ((h (GF := GFx) (F := constOF XB) (γ := γ) (a1 := xt) (a2 := xt)).trans
      (BI.exists_elim fun c => (BI.sep_mono (own_x γ c) (BI.sep_elim_left.trans (xi c))).trans xbad)))))

-- `Iris.iOwn_forall_pred_total` (hypothesis 5): necessary, XB (OrdInc, not IsTotal): B = Unit, φ = True, f = true
theorem w6c4_91 : ¬ drop0% Iris.iOwn_forall_pred_total 5 := fun h => bupd_false_unsound
  (alloc_xt.trans (BIUpdate.mono (BI.exists_elim fun γ =>
    (BI.forall_intro fun _ : Unit => BI.wand_intro BI.sep_elim_left).trans
    ((@h GFx (constOF XB) _ elemX _ Unit γ (fun _ => True) ⟨⟨(), trivial⟩⟩ (fun _ => xt)).trans
      (BI.exists_elim fun c => (BI.sep_mono (own_x γ c)
        ((BI.forall_elim ()).trans (BI.sep_emp.mpr.trans ((BI.sep_mono_right (BI.pure_intro trivial)).trans
          (BI.wand_elim_left.trans (xi c)))))).trans xbad)))))

-- `Iris.iOwn_and_discrete_total` (hypothesis 7): necessary, XB (OrdInc, not IsTotal): a1 = a2 = true, c = false; h vacuous
theorem w6c4_92 : ¬ drop0% Iris.iOwn_and_discrete_total 7 := fun h => bupd_false_unsound
  (alloc_xt.trans (BIUpdate.mono (BI.exists_elim fun γ => (BI.and_intro .rfl .rfl).trans
    ((h (GF := GFx) (F := constOF XB) (γ := γ) (a1 := xt) (a2 := xt) (c := xf)
      (fun c' hv h1 _ => (xb_no_inc c' hv h1).elim)).trans (own_xf_false γ)))))

-- `Iris.iOwn_and_discrete_total_false` (hypothesis 7): necessary, XB (OrdInc, not IsTotal): a1 = a2 = true; h vacuous
theorem w6c4_93 : ¬ drop0% Iris.iOwn_and_discrete_total_false 7 := fun h => bupd_false_unsound
  (alloc_xt.trans (BIUpdate.mono (BI.exists_elim fun γ => (BI.and_intro .rfl .rfl).trans
    (h (GF := GFx) (F := constOF XB) (γ := γ) (a1 := xt) (a2 := xt) (fun c' hv h1 _ => xb_no_inc c' hv h1)))))

-- `Iris.instPersistentIPropIOwnOfCoreIdAp` (hypothesis 6): necessary, XB: own true is not duplicable (true • true = false is invalid)
theorem w6c4_94 : ¬ drop0% Iris.instPersistentIPropIOwnOfCoreIdAp 6 := fun h => bupd_false_unsound
  (alloc_xt.trans (BIUpdate.mono (BI.exists_elim fun γ =>
    (@BI.persistent_sep_dup_mp _ _ _ (h (GF := GFx) (F := constOF XB) (γ := γ) (a := xt))).trans
      ((iOwn_op (GF := GFx) (F := constOF XB) (γ := γ) (a1 := xt) (a2 := xt)).mpr.trans (own_xf_false γ)))))

-- `Iris.unfoldi_bundle_coreId` (hypothesis 5): necessary, XB: true has no core
theorem w6c4_95 : ¬ drop0% Iris.unfoldi_bundle_coreId 5 := fun h => by
  have := (h (GF := GFx) (F := constOF XB) (a := xt)).core_id
  cases this

-- `Iris.iOwn_forall` (hypothesis 4): necessary, Y2 (not OrdInc): f true = a, f false = b, own b ⊢ own a; a and b have no common valid upper bound
theorem w6c4_96 : ¬ drop0% Iris.iOwn_forall 4 := fun h => bupd_false_unsound
  (alloc_yb.trans (BIUpdate.mono (BI.exists_elim fun γ =>
    (BI.forall_intro fun x : Bool => by cases x; exact .rfl; exact (yb_ab γ).trans BI.and_elim_l).trans
    ((h (GF := GFy) (F := constOF Y2) (B := Bool) γ (fun x => bif x then .a else .b)).trans
      (BI.exists_elim fun c => (BI.sep_mono (yv γ c) (BI.and_intro ((BI.forall_elim true).trans (y_incS .a c (by decide)))
        ((BI.forall_elim false).trans (y_incS .b c (by decide))))).trans
        ybad')))))

-- `Iris.iOwn_forall_total` (hypothesis 4): necessary, Y2 (total, not OrdInc): f true = a, f false = b; no valid c includes both
theorem w6c4_97 : ¬ drop0% Iris.iOwn_forall_total 4 := fun h => bupd_false_unsound
  (alloc_yb.trans (BIUpdate.mono (BI.exists_elim fun γ => (yforall γ).trans
    ((h (GF := GFy) (F := constOF Y2) (B := Bool) γ (fun x => bif x then .a else .b)).trans
      (BI.exists_elim fun c => (BI.sep_mono (yv γ c) (BI.and_intro ((BI.forall_elim true).trans (y_inc .a c (by decide)))
        ((BI.forall_elim false).trans (y_inc .b c (by decide))))).trans ybad')))))

-- `Iris.iOwn_and` (hypothesis 5): necessary, Y2 (not OrdInc): a1 = a, a2 = b (own b ⊢ own a)
theorem w6c4_98 : ¬ drop0% Iris.iOwn_and 5 := fun h => bupd_false_unsound
  (alloc_yb.trans (BIUpdate.mono (BI.exists_elim fun γ => (yb_ab γ).trans
    ((h (GF := GFy) (F := constOF Y2) (γ := γ) (a1 := .a) (a2 := .b)).trans
      (BI.exists_elim fun c => (BI.sep_mono (yv γ c) (BI.sep_mono (y_incS .a c (by decide)) (y_incS .b c (by decide)))).trans ybad)))))

-- `Iris.iOwn_and_total` (hypothesis 5): necessary, Y2 (total, not OrdInc): a1 = a, a2 = b
theorem w6c4_99 : ¬ drop0% Iris.iOwn_and_total 5 := fun h => bupd_false_unsound
  (alloc_yb.trans (BIUpdate.mono (BI.exists_elim fun γ => (yb_ab γ).trans
    ((h (GF := GFy) (F := constOF Y2) (γ := γ) (a1 := .a) (a2 := .b)).trans
      (BI.exists_elim fun c => (BI.sep_mono (yv γ c) (BI.sep_mono (y_inc .a c (by decide)) (y_inc .b c (by decide)))).trans ybad)))))

-- `Iris.iOwn_forall_pred` (hypothesis 4): necessary, Y2 (not OrdInc): B = Bool, φ = True, f true = a, f false = b
theorem w6c4_100 : ¬ drop0% Iris.iOwn_forall_pred 4 := fun h => bupd_false_unsound
  (alloc_yb.trans (BIUpdate.mono (BI.exists_elim fun γ => (yforallp γ).trans
    ((@h GFy (constOF Y2) _ elemY Bool γ (fun _ => True) ⟨⟨true, trivial⟩⟩ (fun x => bif x then .a else .b)).trans
      (BI.exists_elim fun c => (BI.sep_mono (yv γ c) (BI.and_intro
        ((BI.forall_elim true).trans ((wpure _).trans (y_incS .a c (by decide))))
        ((BI.forall_elim false).trans ((wpure _).trans (y_incS .b c (by decide)))))).trans ybad')))))

-- `Iris.iOwn_forall_pred_total` (hypothesis 4): necessary, Y2 (total, not OrdInc): B = Bool, φ = True, f true = a, f false = b
theorem w6c4_101 : ¬ drop0% Iris.iOwn_forall_pred_total 4 := fun h => bupd_false_unsound
  (alloc_yb.trans (BIUpdate.mono (BI.exists_elim fun γ => (yforallp γ).trans
    ((@h GFy (constOF Y2) _ elemY _ Bool γ (fun _ => True) ⟨⟨true, trivial⟩⟩ (fun x => bif x then .a else .b)).trans
      (BI.exists_elim fun c => (BI.sep_mono (yv γ c) (BI.and_intro
        ((BI.forall_elim true).trans ((wpure _).trans (y_inc .a c (by decide))))
        ((BI.forall_elim false).trans ((wpure _).trans (y_inc .b c (by decide)))))).trans ybad')))))

-- `Iris.iOwn_and_discrete_total` (hypothesis 6): necessary, Y2 (not OrdInc): a1 = a, a2 = b, c = bot; h vacuous (no valid common upper bound)
theorem w6c4_102 : ¬ drop0% Iris.iOwn_and_discrete_total 6 := fun h => bupd_false_unsound
  (alloc_yb.trans (BIUpdate.mono (BI.exists_elim fun γ => (yb_ab γ).trans
    ((h (GF := GFy) (F := constOF Y2) (γ := γ) (a1 := .a) (a2 := .b) (c := .bot)
      (fun c' hv h1 h2 => (y_no_common c' hv h1 h2).elim)).trans ((yv γ .bot).trans (BI.pure_mono fun h => h rfl))))))

-- `Iris.iOwn_and_discrete_total_false` (hypothesis 6): necessary, Y2 (not OrdInc): a1 = a, a2 = b; h holds (no valid common upper bound)
theorem w6c4_103 : ¬ drop0% Iris.iOwn_and_discrete_total_false 6 := fun h => bupd_false_unsound
  (alloc_yb.trans (BIUpdate.mono (BI.exists_elim fun γ => (yb_ab γ).trans
    (h (GF := GFy) (F := constOF Y2) (γ := γ) (a1 := .a) (a2 := .b) (fun c' hv h1 h2 => y_no_common c' hv h1 h2)))))

-- `Iris.transpAp` (hypothesis 2): necessary, F1 = constOF Unit, F2 = constOF Bool: Unit ≠ Bool
theorem w6c4_104 : ¬ drop0% Iris.transpAp 2 := fun h => by
  have e : Unit = Bool := h (F1 := constOF Unit) (F2 := constOF Bool) (T := Unit)
  have : Subsingleton Bool := e ▸ (inferInstance : Subsingleton Unit)
  exact absurd (Subsingleton.elim true false) (by decide)

-- `Iris.OFE.transpAp_eqv_mp` (hypothesis 11): necessary, F₁ = F₂ = constOF CoPsetDisjL (discrete), x = valid ∅, y = error
theorem w6c4_105 : ¬ drop0% Iris.OFE.transpAp_eqv_mp 11 := fun h => by
  have := h (F₁ := constOF CoPsetDisjL) (F₂ := constOF CoPsetDisjL) (T := Unit) (n := 0) rfl HEq.rfl (x := ce) (y := cr)
  exact nomatch (show ce = cr from this)

-- `Iris.OFE.transpAp_validN_mp` (hypothesis 10): necessary, F₁ = F₂ = constOF CoPsetDisjL, x = error
theorem w6c4_106 : ¬ drop0% Iris.OFE.transpAp_validN_mp 10 := fun h =>
  cr_inv (h (F₁ := constOF CoPsetDisjL) (F₂ := constOF CoPsetDisjL) (T := Unit) (n := 0) rfl HEq.rfl (x := cr))

-- `Iris.OFE.validN_transpAp_mp` (hypothesis 10): necessary, F₁ = F₂ = constOF CoPsetDisjL, x = error
theorem w6c4_107 : ¬ drop0% Iris.OFE.validN_transpAp_mp 10 := fun h =>
  cr_inv (h (F₁ := constOF CoPsetDisjL) (F₂ := constOF CoPsetDisjL) (T := Unit) (n := 0) rfl HEq.rfl (x := cr))

-- `Iris.OFE.transpAp_eqv_mp` (hypothesis 8): necessary, F = constOF (Excl TN) with the truncation OFE (RF₁) and the discrete OFE (RF₂): excl 1, excl 2 agree at 0 only in RF₁
theorem w6c4_108 : ¬ drop0% Iris.OFE.transpAp_eqv_mp 8 := fun h => by
  have := h (F₁ := constOF (Excl TN)) (F₂ := constOF (Excl TN)) (T := Unit)
    (RF₁ := @OFunctor.constOF_RFunctorContractive _ exT) (RF₂ := @OFunctor.constOF_RFunctorContractive _ exD)
    (n := 0) rfl (x := Excl.excl ⟨1⟩) (y := Excl.excl ⟨2⟩) (show min 1 (0+1) = min 2 (0+1) from rfl)
  have e : (⟨1⟩ : TN) = ⟨2⟩ := this
  cases e

-- `Iris.OFE.transpAp_op_mp` (hypothesis 7): necessary, F = constOF XB with op constantly false (RF₁) and op and (RF₂): true • true differs
theorem w6c4_109 : ¬ drop0% Iris.OFE.transpAp_op_mp 7 := fun h => by
  have := h (F₁ := constOF XB) (F₂ := constOF XB) (T := Unit) (RF₁ := RXB) (RF₂ := RXA) rfl (x := xt) (y := xt)
  cases this

-- `Iris.OFE.transpAp_pcore_mp` (hypothesis 7): necessary, F = constOF XB with no core (RF₁) and core true (RF₂)
theorem w6c4_110 : ¬ drop0% Iris.OFE.transpAp_pcore_mp 7 := fun h => by
  have := h (F₁ := constOF XB) (F₂ := constOF XB) (T := Unit) (RF₁ := RXB) (RF₂ := RXC) rfl (x := xt)
  cases this

-- `Iris.OFE.transpAp_validN_mp` (hypothesis 8): necessary, F = constOF XB with all valid (RF₁) and only true valid (RF₂), x = false
theorem w6c4_111 : ¬ drop0% Iris.OFE.transpAp_validN_mp 8 := fun h => by
  have := h (F₁ := constOF XB) (F₂ := constOF XB) (T := Unit) (RF₁ := RXA) (RF₂ := RXB) (n := 0) rfl (x := xf) trivial
  cases (show false = true from this)

-- `Iris.OFE.validN_transpAp_mp` (hypothesis 8): necessary, F = constOF XB with only true valid (RF₁) and all valid (RF₂), x = false
theorem w6c4_112 : ¬ drop0% Iris.OFE.validN_transpAp_mp 8 := fun h => by
  have := h (F₁ := constOF XB) (F₂ := constOF XB) (T := Unit) (RF₁ := RXB) (RF₂ := RXA) (n := 0) rfl (x := xf) trivial
  cases (show false = true from this)

-- `Iris.ElemG.bundle_discreteE` (hypothesis 5): necessary, GFag (Agree SiProp): toAgree sp0 is 0-close to toAgree sp1 but different
theorem w6c4_113 : ¬ drop0% Iris.ElemG.bundle_discreteE 5 := fun h =>
  ag_ne ((h (E := elemAg) (v := toAgree sp0)).discrete ag_dist)

-- `Iris.IProp.unfoldi_discreteE` (hypothesis 3): necessary, GFag (Agree SiProp): toAgree sp0 is 0-close to toAgree sp1 but different
theorem w6c4_114 : ¬ drop0% Iris.IProp.unfoldi_discreteE 3 := fun h =>
  ag_ne ((h (FF := GFag) (τ := 0) (v := toAgree sp0)).discrete ag_dist)

-- `Iris.iSingleton_discreteE` (hypothesis 6): necessary, GFag: the singletons of toAgree sp0 and toAgree sp1 are 0-close but different
theorem w6c4_115 : ¬ drop0% Iris.iSingleton_discreteE 6 := fun h => by
  have e := (h (GF := GFag) (F := constOF (Agree SiProp)) (γ := 0) (v := toAgree sp0)).discrete
    (y := iSingleton (GF := GFag) (constOF (Agree SiProp)) 0 (toAgree sp1)) (OFE.NonExpansive.ne ag_dist)
  have := congrArg (fun r : IResUR GFag => (r (ElemG.τ GFag (constOF (Agree SiProp)))).car 0) e
  simp only [iSingleton, dite_true, GenMap.singleton_map_in] at this
  exact ag_ne (Option.some.inj this)

-- `Iris.iOwn_and_discrete_total_false` (hypothesis 5): necessary, Agree SiProp (not discrete): toAgree sp0, toAgree sp1 have no valid common upper bound but are 0-close (Probe3 p3_37 for the ≼ version)
theorem w6c4_116 : ¬ drop0% Iris.iOwn_and_discrete_total_false 5 := fun h => by
  have H := h (GF := GFag) (F := constOF (Agree SiProp)) (γ := 0) (a1 := toAgree sp0) (a2 := toAgree sp1)
    (fun c' hv h1 h2 => ag_no_ub c' hv (IncOrd.inc_ord h1) (IncOrd.inc_ord h2))
  exact H 0 ⟨sgA 0 (toAgree sp0), ag_valid0⟩ ⟨by unfold iOwn; exact ag_own01.1, by unfold iOwn; exact ag_own01.2⟩

-- `Iris.iOwn_and_discrete_total` (hypothesis 5): necessary, Agree SiProp: a1 = toAgree sp0, a2 = toAgree sp1 (h vacuous), c = toAgree sp2 not owned at step 0
theorem w6c4_117 : ¬ drop0% Iris.iOwn_and_discrete_total 5 := fun h => by
  have H := h (GF := GFag) (F := constOF (Agree SiProp)) (γ := 0) (a1 := toAgree sp0) (a2 := toAgree sp1) (c := toAgree sp2)
    (fun c' hv h1 h2 => (ag_no_ub c' hv (IncOrd.inc_ord h1) (IncOrd.inc_ord h2)).elim)
  have := H 0 ⟨sgA 0 (toAgree sp0), ag_valid0⟩ ⟨by unfold iOwn; exact ag_own01.1, by unfold iOwn; exact ag_own01.2⟩
  unfold iOwn at this
  exact ag_not_own2 this

-- `Iris.iOwn_ord_and_discrete_total` (hypothesis 5): necessary, Agree SiProp: a1 = toAgree sp0, a2 = toAgree sp1 (h vacuous), c = toAgree sp2 not owned at step 0
theorem w6c4_118 : ¬ drop0% Iris.iOwn_ord_and_discrete_total 5 := fun h => by
  have H := h (GF := GFag) (F := constOF (Agree SiProp)) (γ := 0) (a1 := toAgree sp0) (a2 := toAgree sp1) (c := toAgree sp2)
    (fun c' hv h1 h2 => (ag_no_ub c' hv h1 h2).elim)
  have := H 0 ⟨sgA 0 (toAgree sp0), ag_valid0⟩ ⟨by unfold iOwn; exact ag_own01.1, by unfold iOwn; exact ag_own01.2⟩
  unfold iOwn at this
  exact ag_not_own2 this

-- `Iris.bigOpL_iOwn` (hypothesis 8): necessary, GFc, l = []: emp does not entail own γ unit (the unit resource has no entry at γ)
theorem w6c4_119 : ¬ drop0% Iris.bigOpL_iOwn 8 := fun h => by
  have H := (h (GF := GFc) (F := constOF CoPsetDisjL) (E := elemC) (B := Unit) 0 (fun _ _ => ce) []).mpr
  have := ((BI.BigSepL.bigSepL_nil_intro (P := iprop(True))).trans H) 0 ⟨UORA.unit, UORA.unit_valid.validN⟩ trivial
  unfold iOwn at this
  have h3 := this (ElemG.τ GFc (constOF CoPsetDisjL)) 0
  change (some _ : Option CoPsetDisjL) ≼ₒ{0} none at h3
  exact Option.not_some_ordN_none h3

-- `Iris.instCoreIdIResURISingletonOfApIProp` (hypothesis 6): necessary, GFx: true has no core, so its singleton is not a core id
theorem w6c4_120 : ¬ drop0% Iris.instCoreIdIResURISingletonOfApIProp 6 := fun h => by
  have := (h (GF := GFx) (F := constOF XB) (γ := 0) (a := xt)).core_id
  have e := congrArg (Option.map fun r : IResUR GFx => (r (ElemG.τ GFx (constOF XB))).car 0) this
  change some (none : Option XB) = some (some xt) at e
  cases e

-- `Iris.bigOpM_iOwn` (hypothesis 12): necessary, GFc, m = ∅ (ExtTreeMap over Nat): emp does not entail own γ of anything
theorem w6c4_121 : ¬ drop0% Iris.bigOpM_iOwn 12 := fun h =>
  own_not_unit 0 _ (((BI.BigSepM.bigSepM_empty_intro (P := iprop(True))).trans
    (h (GF := GFc) (F := constOF CoPsetDisjL) (E := elemC) (M := fun V => Std.ExtTreeMap Nat V compare) (K := Nat) (B := Unit)
      0 (fun _ _ => ce) ∅).mpr) 0 ⟨UORA.unit, UORA.unit_valid.validN⟩ trivial)

-- `Iris.bigOpS_iOwn` (hypothesis 10): necessary, GFc, X = ∅ (ExtTreeSet Nat): emp does not entail own γ of anything
theorem w6c4_122 : ¬ drop0% Iris.bigOpS_iOwn 10 := fun h =>
  own_not_unit 0 _ (((BI.BigSepS.bigSepS_empty_intro (P := iprop(True))).trans
    (h (GF := GFc) (F := constOF CoPsetDisjL) (E := elemC) (B := Nat) (S := Std.ExtTreeSet Nat compare)
      0 (fun _ => ce) ∅).mpr) 0 ⟨UORA.unit, UORA.unit_valid.validN⟩ trivial)

-- `Iris.bigOpMS_iOwn` (hypothesis 10): necessary, GFc, X = ∅ (ListPerm Nat): emp does not entail own γ of anything
theorem w6c4_123 : ¬ drop0% Iris.bigOpMS_iOwn 10 := fun h =>
  own_not_unit 0 _ (((BI.BigSepMS.bigSepMS_empty_intro (P := iprop(True))).trans
    (h (GF := GFc) (F := constOF CoPsetDisjL) (E := elemC) (B := Nat) (MS := Iris.Std.ListPerm Nat)
      0 (fun _ => ce) ∅).mpr) 0 ⟨UORA.unit, UORA.unit_valid.validN⟩ trivial)

-- `Iris.iOwn_timeless` (hypothesis 6): necessary, GFag: a = toAgree sp0 (not discrete); at step 1 over the singleton of toAgree sp1, ▷ own a holds but own a fails
theorem w6c4_124 : ¬ drop0% Iris.iOwn_timeless 6 := fun h => by
  have H := (h (GF := GFag) (F := constOF (Agree SiProp)) (γ := 0) (a := toAgree sp0)).timeless
  have hv1 : ✓{1} sgA 0 (toAgree sp1) := validN_iSingleton.mpr Agree.toAgree_validN
  have hd : iSingleton (GF := GFag) (constOF (Agree SiProp)) 0 (toAgree sp0) ≡{0}≡ iSingleton (GF := GFag) (constOF (Agree SiProp)) 0 (toAgree sp1) :=
    OFE.NonExpansive.ne (OFE.NonExpansive.ne @sp_dist0)
  have hr := Ordered.ordN_of_ord 0 (OrderRefl.ord_refl (sgA 0 (toAgree sp1)))
  have := H 1 ⟨sgA 0 (toAgree sp1), hv1⟩ (by unfold iOwn; exact Ordered.ordN_ne hd.symm .rfl hr)
  rcases this with hf | ho
  · exact hf
  · unfold iOwn at ho
    have h3 := ho (ElemG.τ GFag (constOF (Agree SiProp))) 0
    change (some (toAgree sp0) : Option (Agree SiProp)) ≼ₒ{1} some (toAgree sp1) at h3
    have h4 : toAgree sp0 ≼ₒ{1} toAgree sp1 := by
      rcases Option.some_ordN_some_iff.mp h3 with h5 | h5
      · exact Ordered.ordN_ne h5.symm .rfl (Ordered.ordN_of_ord 1 (OrderRefl.ord_refl _))
      · exact h5
    have h5 : sp0 ≡{1}≡ sp1 := Agree.toAgree_ordN.mp h4
    have h6 := (h5 (Nat.le_refl 1)).2 trivial
    exact absurd (show (1 : Nat) = 0 from h6) (by decide)
