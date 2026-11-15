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

set_option linter.constructorNameAsVariable false
namespace W3c4
open Iris Iris.OFE

/-- Truncation OFE on naturals (copy of Probe1's TN): 1 and 2 agree at step 0 only. -/
structure TN where v : Nat
instance tnOFE : OFE TN where
  Dist n x y := min x.v (n+1) = min y.v (n+1)
  dist_eqv := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩
  eq_dist' {x y} := ⟨fun h n => h ▸ rfl, fun h => by
      cases x with | mk a => cases y with | mk b =>
      have h' : min a (a+b+1) = min b (a+b+1) := h (a+b)
      simp only [TN.mk.injEq]; omega⟩
  dist_lt {n x y m} h hm := by
    have h' : min x.v (n+1) = min y.v (n+1) := h
    show min x.v (m+1) = min y.v (m+1); omega
theorem tn12 : (⟨1⟩ : TN) ≡{0}≡ ⟨2⟩ := rfl
theorem tn12ne : (⟨1⟩ : TN) ≠ ⟨2⟩ := by simp

/-- Two-element UORA (copy of W1c0's NA): e unit, a idempotent, equality order, all valid. -/
inductive NA | e | a deriving DecidableEq
def NA.op : NA → NA → NA
  | .e, y => y
  | .a, _ => .a
instance : OFE NA := OFE.ofDiscrete NA
instance : OFE.Discrete NA := ⟨id⟩
@[instance_reducible] def naData : DiscreteORAData NA where
  pcore := fun _ => some .e
  op := NA.op
  Valid := fun _ => True
  Order := Eq
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
  pcore_op_left := by intro x cx h; cases h; cases x <;> rfl
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := fun _ _ _ => trivial
  ord_trans := fun _ _ _ h1 h2 => h1.trans h2
  op_mono_left := by intro x y z h; cases h; rfl
  valid_of_ord := fun _ _ _ _ => trivial
  pcore_mono := by intro x y cx h1 h2; exact ⟨.e, rfl, by cases h2; rfl⟩
  pcore_order_op := by intro x cx h y; exact ⟨.e, rfl, by cases h; rfl⟩
  pcore_increasing := by intro x cx h y; cases h; rfl
  increasing_closed := by intro x y _ h; cases h; assumption
instance naORA : ORA NA := ORA.ofDiscreteORAData naData
instance : ORA.Discrete NA := ORA.ofDiscreteORAData_discrete naData
instance : OrderRefl NA := ⟨fun x => show x = x from rfl⟩
instance naUORA : UORA NA where
  unit := .e
  unit_valid := trivial
  unit_left_id := rfl
  pcore_unit := rfl

/-- In NA, a is not increasing (e is not below a • e = a). -/
theorem na_a_not_inc : ¬ Increasing NA.a := fun h => nomatch (h.increasing NA.e : NA.e = NA.a)

/-- Three elements (copy of W1c0's TX): e unit, a idempotent, z absorbing and the only invalid one;
order x ≤ y iff y = z or x ≠ z. a ≤ e but a is not included in e: IncOrd, not OrdInc. -/
inductive TX | e | a | z deriving DecidableEq
def TX.op : TX → TX → TX
  | .e, y => y
  | x, .e => x
  | .a, .a => .a
  | _, _ => .z
instance : OFE TX := OFE.ofDiscrete TX
instance : OFE.Discrete TX := ⟨id⟩
@[instance_reducible] def txData : DiscreteORAData TX where
  pcore := fun _ => some .e
  op := TX.op
  Valid := fun x => x ≠ .z
  Order := fun x y => y = .z ∨ x ≠ .z
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
  pcore_op_left := by intro x cx h; cases h; cases x <;> rfl
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := by intro x y; cases x <;> cases y <;> decide
  ord_trans := by intro x y z; cases x <;> cases y <;> cases z <;> decide
  op_mono_left := by intro x y z; cases x <;> cases y <;> cases z <;> decide
  valid_of_ord := by intro x y; cases x <;> cases y <;> decide
  pcore_mono := by intro x y cx h1 h2; cases h2; exact ⟨.e, rfl, by decide⟩
  pcore_order_op := by intro x cx h y; cases h; exact ⟨.e, rfl, by decide⟩
  pcore_increasing := by intro x cx h y; cases h; cases y <;> decide
  increasing_closed := by intro x y _ _ w; cases y <;> cases w <;> decide
instance txORA : ORA TX := ORA.ofDiscreteORAData txData
instance : ORA.Discrete TX := ORA.ofDiscreteORAData_discrete txData
instance : OrderRefl TX := ⟨fun x => show x = .z ∨ x ≠ .z by cases x <;> decide⟩
instance txUORA : UORA TX where
  unit := .e
  unit_valid := show TX.e ≠ .z by decide
  unit_left_id := rfl
  pcore_unit := rfl
instance txIncOrd : IncOrd TX := ⟨fun {x y} ⟨w, h⟩ => by
  subst h; show TX.op x w = .z ∨ x ≠ .z; cases x <;> cases w <;> decide⟩
theorem tx_z_inv (n : Nat) : ¬ ✓{n} TX.z := fun h => (h : TX.z ≠ .z) rfl
theorem tx_e_val (n : Nat) : ✓{n} TX.e := (show TX.e ≠ .z by decide)
theorem tx_zz (n : Nat) : TX.z ≼ₒ{n} TX.z := (Or.inl rfl : TX.z = .z ∨ TX.z ≠ .z)
theorem tx_ae (n : Nat) : TX.a ≼ₒ{n} TX.e := (Or.inr (by decide) : TX.e = .z ∨ TX.a ≠ .z)
theorem tx_le_e {n : Nat} {x : TX} (h : x ≼{n} TX.e) : x = TX.e := by
  obtain ⟨w, hw⟩ := h; cases x <;> cases w <;> first | rfl | exact nomatch (hw : TX.e = _)

/-- Three elements e (unit), a, z with every product of non-units z; equality order, all valid:
a • a = z but a is not below z, so not IncOrd. -/
inductive E3 | e | a | z deriving DecidableEq
def E3.op : E3 → E3 → E3
  | .e, y => y
  | x, .e => x
  | _, _ => .z
instance : OFE E3 := OFE.ofDiscrete E3
instance : OFE.Discrete E3 := ⟨id⟩
@[instance_reducible] def e3Data : DiscreteORAData E3 where
  pcore := fun _ => some .e
  op := E3.op
  Valid := fun _ => True
  Order := Eq
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
  pcore_op_left := by intro x cx h; cases h; cases x <;> rfl
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := fun _ _ _ => trivial
  ord_trans := fun _ _ _ h1 h2 => h1.trans h2
  op_mono_left := by intro x y z h; cases h; rfl
  valid_of_ord := fun _ _ _ _ => trivial
  pcore_mono := by intro x y cx h1 h2; exact ⟨.e, rfl, by cases h2; rfl⟩
  pcore_order_op := by intro x cx h y; exact ⟨.e, rfl, by cases h; rfl⟩
  pcore_increasing := by intro x cx h y; cases h; cases y <;> rfl
  increasing_closed := by intro x y _ h; cases h; assumption
instance e3ORA : ORA E3 := ORA.ofDiscreteORAData e3Data
instance : OrderRefl E3 := ⟨fun x => show x = x from rfl⟩
instance e3UORA : UORA E3 where
  unit := .e
  unit_valid := trivial
  unit_left_id := rfl
  pcore_unit := rfl

/-- The validity relation `R n _ b := ✓{n} b` is a view relation over any UORA (auth part Unit). -/
def vRel (B : Type) [UORA B] : ViewRel Unit B := fun n _ b => ✓{n} b
instance vRelIs (B : Type) [UORA B] : IsViewRel (vRel B) where
  mono h _ hb hn := ORA.validN_of_ordN hb (ORA.validN_of_le hn h)
  op_left h := ORA.validN_op_left h
  rel_validN _ _ _ h := h
  rel_unit n := ⟨(), ORA.valid_iff_validN.mp UORA.unit_valid n⟩
instance vRelTX : IsViewRelDiscrete (vRel TX) where
  discrete _ _ _ h := h

/-- `R n a _ := a = NA.a` over the discrete NA: a view relation depending on the auth part. -/
def aRel : ViewRel NA Unit := fun _ a _ => a = .a
instance aRelIs : IsViewRel aRel where
  mono h ha _ _ := (show _ = _ from ha) ▸ h
  op_left h := h
  rel_validN _ _ _ _ := trivial
  rel_unit _ := ⟨.a, rfl⟩

/-- `R n a _ := n = 0 ∨ a = NA.a`: a view relation that is not discrete (fails at e for n ≥ 1). -/
def zRel : ViewRel NA Unit := fun n a _ => n = 0 ∨ a = .a
instance zRelIs : IsViewRel zRel where
  mono {n1 a1 b1 n2 a2 b2} h ha _ hn := by
    have : a1 = a2 := ha
    subst this; rcases h with h | h
    · exact .inl (by omega)
    · exact .inr h
  op_left h := h
  rel_validN _ _ _ _ := trivial
  rel_unit _ := ⟨.a, .inr rfl⟩

/-- The empty relation is not a view relation (no unit). -/
def fRel : ViewRel Unit Unit := fun _ _ _ => False
theorem noVR : ¬ IsViewRel fRel := fun h => (h.rel_unit 0).elim fun _ h => h

instance : ORA.CoreId (() : Unit) := ⟨rfl⟩

abbrev TS := Std.ExtTreeSet Nat compare
abbrev TM := fun V => Std.ExtTreeMap Nat V compare
abbrev MSN := Iris.Std.ListPerm Nat

theorem tx_ae' : TX.a ≼ₒ TX.e := (Or.inr (by decide) : TX.e = .z ∨ TX.a ≠ .z)

/-- The full relation on TN × Unit: a discrete view relation over a non-discrete auth OFE. -/
def tRel : ViewRel TN Unit := fun _ _ _ => True
instance tRelIs : IsViewRelDiscrete tRel where
  mono _ _ _ _ := trivial
  op_left _ := trivial
  rel_validN _ _ _ _ := trivial
  rel_unit _ := ⟨⟨0⟩, trivial⟩
  discrete _ _ _ _ := trivial

/-- `vRel` over the non-discrete UORA `Option (Excl TN)` is discrete (Excl validity ignores the step). -/
instance vRelXT : IsViewRelDiscrete (vRel (Option (Excl TN))) where
  discrete n a b h := by
    rcases b with _ | (_ | _)
    · exact trivial
    · exact trivial
    · exact h.elim

theorem map'_toAgree {α β : Type} [OFE α] [OFE β] (f : α → β) (x : α) :
    Agree.map' f (toAgree x) = toAgree (f x) := rfl

/-- A map on TN that is not non-expansive: 1 ↦ 0, everything else ↦ 1. -/
def bad (x : TN) : TN := if x.v = 1 then ⟨0⟩ else ⟨1⟩
theorem bad12 : ¬ (bad ⟨1⟩ ≡{0}≡ bad ⟨2⟩) := fun h => by
  have : min (bad ⟨1⟩).v 1 = min (bad ⟨2⟩).v 1 := h
  simp [bad] at this

/-- Two auth views over TN that agree at step 0 but differ. -/
theorem auth12 {B : Type} [OFE B] {R : ViewRel TN B} (b : B) :
    (⟨some (DFrac.own 1, toAgree ⟨1⟩), b⟩ : View R) ≡{0}≡ ⟨some (DFrac.own 1, toAgree ⟨2⟩), b⟩ :=
  ⟨some_dist_some.mpr ⟨OFE.Dist.rfl, toAgree.ne.ne tn12⟩, OFE.Dist.rfl⟩
theorem auth12ne {B : Type} {R : ViewRel TN B} (b : B) :
    (⟨some (DFrac.own 1, toAgree ⟨1⟩), b⟩ : View R) ≠ ⟨some (DFrac.own 1, toAgree ⟨2⟩), b⟩ := fun h => by
  have := congrArg (fun v : View R => v.auth.map Prod.snd) h
  simp only [Option.map_some, Option.some.injEq] at this
  exact tn12ne (Agree.toAgree_inj this)

end W3c4
open Iris Iris.OFE W3c4

-- `IsViewRel.mono` idx 5: necessary (A = B = Unit, R n _ _ := n = 1; n1 = 1, n2 = 0)
theorem w3c4_0 : ¬ drop0% IsViewRel.mono 5 := fun h =>
  absurd (@h Unit Unit _ _ (fun n _ _ => n = 1) 1 () () 0 () () rfl OFE.Dist.rfl
    (by first | trivial | exact Ordered.ordN_of_ord 0 (OrderRefl.ord_refl ())) (Nat.zero_le 1)) (by decide)

-- `IsViewRel.mono` idx 12: necessary (validity relation on TX, b1 = b2 = z invalid)
theorem w3c4_1 : ¬ drop0% IsViewRel.mono 12 := fun h =>
  tx_z_inv 0 (@h Unit TX _ _ (vRel TX) _ 0 () .z 0 () .z OFE.Dist.rfl (tx_zz 0) (Nat.le_refl 0))

-- `IsViewRel.mono` idx 13: necessary (A = NA discrete, R n a _ := a = NA.a; a1 = a, a2 = e)
theorem w3c4_2 : ¬ drop0% IsViewRel.mono 13 := fun h =>
  nomatch (@h NA Unit _ _ aRel _ 0 .a () 0 .e () rfl
    (by first | trivial | exact Ordered.ordN_of_ord 0 (OrderRefl.ord_refl ())) (Nat.le_refl 0) : NA.e = NA.a)

-- `IsViewRel.mono` idx 14: necessary (validity relation on TX, b1 = e valid, b2 = z invalid)
theorem w3c4_3 : ¬ drop0% IsViewRel.mono 14 := fun h =>
  tx_z_inv 0 (@h Unit TX _ _ (vRel TX) _ 0 () .e 0 () .z (tx_e_val 0) OFE.Dist.rfl (Nat.le_refl 0))

-- `IsViewRel.op_left` idx 5: necessary (B = NA, R _ _ x := x = a; b = e, c = a)
theorem w3c4_4 : ¬ drop0% IsViewRel.op_left 5 := fun h =>
  nomatch (@h Unit NA inferInstance inferInstance (fun _ _ x => x = NA.a) 0 () .e .a rfl : NA.e = NA.a)

-- `IsViewRel.op_left` idx 10: necessary (validity relation on TX, b = z, c = e)
theorem w3c4_5 : ¬ drop0% IsViewRel.op_left 10 := fun h =>
  tx_z_inv 0 (@h Unit TX _ _ (vRel TX) _ 0 () .z .e)

-- `IsViewRel.rel_validN` idx 5: necessary (full relation on TX, b = z invalid)
theorem w3c4_6 : ¬ drop0% IsViewRel.rel_validN 5 := fun h =>
  tx_z_inv 0 (@h Unit TX inferInstance inferInstance (fun _ _ _ => True) 0 () .z trivial)

-- `IsViewRel.rel_validN` idx 9: necessary (validity relation on TX, b = z)
theorem w3c4_7 : ¬ drop0% IsViewRel.rel_validN 9 := fun h =>
  tx_z_inv 0 (@h Unit TX _ _ (vRel TX) _ 0 () .z)

-- `IsViewRel.rel_unit` idx 5: necessary (empty relation)
theorem w3c4_8 : ¬ drop0% IsViewRel.rel_unit 5 := fun h =>
  (@h Unit Unit inferInstance inferInstance fRel 0).elim fun _ h => h

-- `IsViewRel.ofMonoOrd` idx 4: necessary (B = E3 with equality order, not IncOrd; R = {e, z}: a • a = z related, a not)
theorem w3c4_9 : ¬ drop0% IsViewRel.ofMonoOrd 4 := fun h => by
  have hv := @h Unit E3 _ _ (fun _ _ x => x = .e ∨ x = .z)
    (fun {n1 a1 b1 n2 a2 b2} hr _ hb _ => (show b2 = b1 from hb) ▸ hr) (fun _ _ _ _ => trivial) (fun _ => ⟨(), .inl rfl⟩)
  have := hv.op_left (n := 0) (a := ()) (b := E3.a) (c := E3.a) (.inr rfl)
  rcases this with h | h <;> exact nomatch h

-- `IsViewRel.ofMonoOrd` idx 6: necessary (A = NA, B = Unit, R n a _ := n = 1 or a = NA.a: not monotone in n)
theorem w3c4_10 : ¬ drop0% IsViewRel.ofMonoOrd 6 := fun h => by
  have hv := @h NA Unit _ _ _ (fun n a _ => n = 1 ∨ a = .a) (fun _ _ _ _ => trivial) (fun _ => ⟨.a, .inr rfl⟩)
  have := hv.mono (n1 := 1) (a1 := NA.e) (b1 := ()) (n2 := 0) (a2 := .e) (b2 := ()) (.inl rfl) OFE.Dist.rfl
    (by first | trivial | exact Ordered.ordN_of_ord 0 (OrderRefl.ord_refl ())) (Nat.zero_le 1)
  rcases this with h | h <;> exact nomatch h

-- `IsViewRel.ofMonoOrd` idx 7: necessary (B = TX (IncOrd), full relation relates the invalid z)
theorem w3c4_11 : ¬ drop0% IsViewRel.ofMonoOrd 7 := fun h => by
  have hv := @h Unit TX _ _ _ (fun _ _ _ => True) (fun _ _ _ _ => trivial) (fun _ => ⟨(), trivial⟩)
  exact tx_z_inv 0 (hv.rel_validN 0 () .z trivial)

-- `IsViewRel.ofMonoOrd` idx 8: necessary (empty relation, no unit)
theorem w3c4_12 : ¬ drop0% IsViewRel.ofMonoOrd 8 := fun h =>
  noVR (@h Unit Unit _ _ _ fRel (fun h => h.elim) (fun _ _ _ h => h.elim))

-- `IsViewRel.ofMonoInc` idx 4: necessary (B = TX, not OrdInc; R _ _ x := x = e is inclusion-closed, a ≼ₒ e but a ≠ e)
theorem w3c4_13 : ¬ drop0% IsViewRel.ofMonoInc 4 := fun h => by
  have hv := @h Unit TX _ _ (fun _ _ x => x = .e)
    (fun {n1 a1 b1 n2 a2 b2} hr _ hb _ => by subst hr; exact tx_le_e hb) (fun _ _ _ hr => hr ▸ tx_e_val _) (fun _ => ⟨(), rfl⟩)
  exact nomatch (hv.mono (n1 := 0) (a1 := ()) (b1 := TX.e) (n2 := 0) (a2 := ()) (b2 := TX.a) rfl OFE.Dist.rfl (tx_ae 0)
    (Nat.le_refl 0) : TX.a = TX.e)

-- `IsViewRel.ofMonoInc` idx 6: necessary (A = NA, B = Unit, R n a _ := n = 1 or a = NA.a: not monotone in n)
theorem w3c4_14 : ¬ drop0% IsViewRel.ofMonoInc 6 := fun h => by
  have hv := @h NA Unit _ _ _ (fun n a _ => n = 1 ∨ a = .a) (fun _ _ _ _ => trivial) (fun _ => ⟨.a, .inr rfl⟩)
  have := hv.mono (n1 := 1) (a1 := NA.e) (b1 := ()) (n2 := 0) (a2 := .e) (b2 := ()) (.inl rfl) OFE.Dist.rfl
    (by first | trivial | exact Ordered.ordN_of_ord 0 (OrderRefl.ord_refl ())) (Nat.zero_le 1)
  rcases this with h | h <;> exact nomatch h

-- `IsViewRel.ofMonoInc` idx 7: necessary (B = Option (Excl Unit), OrdInc; full relation relates the invalid some invalid)
theorem w3c4_15 : ¬ drop0% IsViewRel.ofMonoInc 7 := fun h => by
  have hv := @h Unit (Option (Excl Unit)) _ _ _ (fun _ _ _ => True) (fun _ _ _ _ => trivial) (fun _ => ⟨(), trivial⟩)
  exact (hv.rel_validN 0 () (some .invalid) trivial : False)

-- `IsViewRel.ofMonoInc` idx 8: necessary (empty relation, no unit)
theorem w3c4_16 : ¬ drop0% IsViewRel.ofMonoInc 8 := fun h =>
  noVR (@h Unit Unit _ _ _ fRel (fun h => h.elim) (fun _ _ _ h => h.elim))

-- `IsViewRel.mono_inc` idx 11: necessary (A = B = Unit, R n _ _ := n = 1; n1 = 1, n2 = 0)
theorem w3c4_17 : ¬ drop0% IsViewRel.mono_inc 11 := fun h =>
  absurd (@h Unit Unit 1 () () 0 () () _ _ (fun n _ _ => n = 1) rfl OFE.Dist.rfl (ORA.incN_refl _) (Nat.zero_le 1)) (by decide)

-- `IsViewRel.mono_inc` idx 12: necessary (validity relation on TX, b1 = b2 = z)
theorem w3c4_18 : ¬ drop0% IsViewRel.mono_inc 12 := fun h =>
  tx_z_inv 0 (@h Unit TX 0 () .z 0 () .z _ _ (vRel TX) _ OFE.Dist.rfl (ORA.incN_refl _) (Nat.le_refl 0))

-- `IsViewRel.mono_inc` idx 13: necessary (A = NA, R n a _ := a = NA.a; a1 = a, a2 = e)
theorem w3c4_19 : ¬ drop0% IsViewRel.mono_inc 13 := fun h =>
  nomatch (@h NA Unit 0 .a () 0 .e () _ _ aRel _ rfl (ORA.incN_refl _) (Nat.le_refl 0) : NA.e = NA.a)

-- `IsViewRel.mono_inc` idx 14: necessary (validity relation on TX, b1 = e, b2 = z)
theorem w3c4_20 : ¬ drop0% IsViewRel.mono_inc 14 := fun h =>
  tx_z_inv 0 (@h Unit TX 0 () .e 0 () .z _ _ (vRel TX) _ (tx_e_val 0) OFE.Dist.rfl (Nat.le_refl 0))

-- `IsViewRelDiscrete.toIsViewRel` idx 5: necessary (empty relation)
theorem w3c4_21 : ¬ drop0% IsViewRelDiscrete.toIsViewRel 5 := fun h => noVR (@h Unit Unit _ _ fRel)

-- `IsViewRelDiscrete.discrete` idx 5: necessary (R n _ _ := n = 0)
theorem w3c4_22 : ¬ drop0% IsViewRelDiscrete.discrete 5 := fun h =>
  absurd (@h Unit Unit inferInstance inferInstance (fun n _ _ => n = 0) 1 () () rfl) (by decide)

-- `IsViewRelDiscrete.discrete` idx 9: necessary (validity relation on TX is discrete; b = z)
theorem w3c4_23 : ¬ drop0% IsViewRelDiscrete.discrete 9 := fun h =>
  tx_z_inv 0 (@h Unit TX _ _ (vRel TX) _ 0 () .z)

-- `ViewRel.iff_of_dist` idx 5: necessary (A = TN, R _ a _ := a = 1; a1 = 1, a2 = 2 agree at 0)
theorem w3c4_24 : ¬ drop0% ViewRel.iff_of_dist 5 := fun h =>
  tn12ne ((@h TN Unit _ _ (fun _ a _ => a = ⟨1⟩) 0 ⟨1⟩ ⟨2⟩ () () tn12 OFE.Dist.rfl).mp rfl).symm

-- `ViewRel.iff_of_dist` idx 11: necessary (A = NA, R _ a _ := a = NA.a; a1 = a, a2 = e)
theorem w3c4_25 : ¬ drop0% ViewRel.iff_of_dist 11 := fun h =>
  nomatch ((@h NA Unit _ _ aRel _ 0 .a .e () () OFE.Dist.rfl).mp rfl : NA.e = NA.a)

-- `ViewRel.iff_of_dist` idx 12: necessary (validity relation on TX, b1 = e, b2 = z)
theorem w3c4_26 : ¬ drop0% ViewRel.iff_of_dist 12 := fun h =>
  tx_z_inv 0 ((@h Unit TX _ _ (vRel TX) _ 0 () () .e .z OFE.Dist.rfl).mp (tx_e_val 0))

-- `View.discrete` idx 7: necessary (A = TN: auth toAgree 1 is not discrete)
theorem w3c4_27 : ¬ drop0% View.discrete 7 := fun h =>
  auth12ne (R := tRel) () ((@h TN Unit _ _ tRel () (some (DFrac.own 1, toAgree ⟨1⟩)) inferInstance).discrete (auth12 ()))

-- `View.instDiscrete` idx 5: necessary (A = TN not discrete, B = Unit)
theorem w3c4_28 : ¬ drop0% View.instDiscrete 5 := fun h =>
  auth12ne (R := tRel) () ((@h TN Unit _ _ tRel _).discrete_0 (auth12 ()))

-- `View.instDiscrete` idx 6: necessary (B = TN not discrete: fragments 1 and 2)
theorem w3c4_29 : ¬ drop0% View.instDiscrete 6 := fun h =>
  tn12ne (congrArg View.frag ((@h Unit TN _ _ (fun _ _ _ => True) _).discrete_0
    (x := ⟨none, ⟨1⟩⟩) (y := ⟨none, ⟨2⟩⟩) ⟨OFE.Dist.rfl, tn12⟩))

-- `View.auth_inj_frac` idx 11: necessary (q1 = own 1, q2 = discard)
theorem w3c4_30 : ¬ drop0% View.auth_inj_frac 11 := fun h =>
  nomatch (@h Unit Unit _ _ (fun _ _ _ => True) _ (.own 1) .discard () () 0)

-- `View.dist_of_auth_dist` idx 11: necessary (A = NA discrete, a1 = e, a2 = a)
theorem w3c4_31 : ¬ drop0% View.dist_of_auth_dist 11 := fun h =>
  nomatch (@h NA Unit _ _ (fun _ _ _ => True) _ .discard .discard .e .a 0 : NA.e = NA.a)

-- `View.auth_dist_inj` idx 11: necessary (A = NA discrete, a1 = e, a2 = a)
theorem w3c4_32 : ¬ drop0% View.auth_dist_inj 11 := fun h =>
  nomatch ((@h NA Unit _ _ (fun _ _ _ => True) _ .discard .discard .e .a 0).2 : NA.e = NA.a)

-- `View.auth_eqv_inj` idx 10: necessary (q1 = own 1, q2 = discard)
theorem w3c4_33 : ¬ drop0% View.auth_eqv_inj 10 := fun h =>
  nomatch (@h Unit Unit _ _ (fun _ _ _ => True) _ (.own 1) .discard () ()).1

-- `View.frag_eqv_inj` idx 8: necessary (B = NA, b1 = e, b2 = a)
theorem w3c4_34 : ¬ drop0% View.frag_eqv_inj 8 := fun h =>
  nomatch (@h Unit NA _ _ (fun _ _ _ => True) _ .e .a)

-- `View.IsViewRel.of_agree_dist_iff` idx 5: necessary (A = TN, R _ a _ := a = 1, a = 2: toAgree 2 agrees with toAgree 1 at 0)
theorem w3c4_35 : ¬ drop0% View.IsViewRel.of_agree_dist_iff 5 := fun h =>
  tn12ne ((@h TN Unit _ _ (fun _ a _ => a = ⟨1⟩) 0 () () ⟨2⟩ OFE.Dist.rfl).mp ⟨⟨1⟩, toAgree.ne.ne tn12.symm, rfl⟩).symm

-- `View.IsViewRel.of_agree_dist_iff` idx 10: necessary (validity relation on TX, b' = z, b = e)
theorem w3c4_36 : ¬ drop0% View.IsViewRel.of_agree_dist_iff 10 := fun h =>
  ((@h Unit TX _ _ (vRel TX) _ 0 .z .e ()).mpr (tx_e_val 0)).elim fun _ h => tx_z_inv 0 h.2

-- `View.ValidN.pair` idx 5: necessary (full relation on TX, x = fragment z)
theorem w3c4_37 : ¬ drop0% View.ValidN.pair 5 := fun h =>
  tx_z_inv 0 (@h Unit TX _ _ (fun _ _ _ => True) 0 ⟨none, .z⟩ ⟨(), trivial⟩).2

-- `View.ValidN.pair` idx 8: necessary (validity relation on TX, x = fragment z)
theorem w3c4_38 : ¬ drop0% View.ValidN.pair 8 := fun h =>
  tx_z_inv 0 (@h Unit TX _ _ (vRel TX) _ 0 ⟨none, .z⟩).2

-- `View.increasing_auth` idx 6: removable (Option (DFrac × Agree A) is IncOrd, so every auth part is increasing)
theorem w3c4_39 : drop% View.increasing_auth 6 := by
  intros; exact IncOrd.increasing _

-- `View.increasing_frag` idx 6: necessary (B = NA: fragment a is not increasing)
theorem w3c4_40 : ¬ drop0% View.increasing_frag 6 := fun h =>
  na_a_not_inc (@h Unit NA _ _ (fun _ _ _ => True) ⟨none, .a⟩)

-- `View.increasing_mk` idx 6: removable (the auth part is always increasing: Option (DFrac × Agree A) is IncOrd)
theorem w3c4_41 : drop% View.increasing_mk 6 := by
  intro A B _ _ R v hb; exact View.increasing_mk (IncOrd.increasing _) hb

-- `View.increasing_mk` idx 7: necessary (B = NA, v = fragment a)
theorem w3c4_42 : ¬ drop0% View.increasing_mk 7 := fun h =>
  na_a_not_inc (View.increasing_frag (@h Unit NA _ _ (fun _ _ _ => True) ⟨none, .a⟩ (IncOrd.increasing _)))

-- `View.instIncOrd` idx 6: necessary (B = NA not IncOrd: fragment a is not increasing)
theorem w3c4_44 : ¬ drop0% View.instIncOrd 6 := fun h =>
  na_a_not_inc (View.increasing_frag (v := (◯V NA.a : View (vRel NA)))
    (by exact @IncOrd.increasing _ _ _ _ (@h Unit NA _ _ (vRel NA) _) (◯V NA.a)))

-- `View.instOrdInc` idx 6: necessary (B = TX not OrdInc: fragment a ≼ₒ fragment e, not included)
theorem w3c4_46 : ¬ drop0% View.instOrdInc 6 := fun h => by
  obtain ⟨w, hw⟩ := (@h Unit TX _ _ (vRel TX) _).ord_inc (View.frag_ord_of_ord (R := vRel TX) tx_ae')
  have h2 : TX.e = TX.op .a w.frag := congrArg View.frag hw
  revert h2; generalize w.frag = c; cases c <;> intro h <;> exact absurd h (by decide)

-- `View.instIsInc` idx 6: necessary (B = NA not IncOrd: fragment a is not increasing)
theorem w3c4_48 : ¬ drop0% View.instIsInc 6 := fun h =>
  na_a_not_inc (View.increasing_frag (v := (◯V NA.a : View (vRel NA)))
    (by exact @IncOrd.increasing _ _ _ _ (@h Unit NA _ _ (vRel NA) _).toIncOrd (◯V NA.a)))

-- `View.increasing_fragElem` idx 7: necessary (B = NA, b = a)
theorem w3c4_51 : ¬ drop0% View.increasing_fragElem 7 := fun h =>
  na_a_not_inc (View.increasing_frag (@h Unit NA _ _ (vRel NA) _ .a))

-- `View.instDiscreteOfDiscreteOfIsViewRelDiscrete` idx 5: removable (IsViewRel R follows from the binder IsViewRelDiscrete R)
theorem w3c4_52 : indep% View.instDiscreteOfDiscreteOfIsViewRelDiscrete 5 := by
  intros; exact IsViewRelDiscrete.toIsViewRel

-- `View.instDiscreteOfDiscreteOfIsViewRelDiscrete` idx 6: necessary (A = TN not discrete, full relation)
theorem w3c4_53 : ¬ drop0% View.instDiscreteOfDiscreteOfIsViewRelDiscrete 6 := fun h =>
  auth12ne (R := tRel) () ((@h TN Unit _ _ tRel _ _ _).discrete_0 (auth12 ()))

-- `View.instDiscreteOfDiscreteOfIsViewRelDiscrete` idx 7: necessary (B = Option (Excl TN) not discrete)
theorem w3c4_54 : ¬ drop0% View.instDiscreteOfDiscreteOfIsViewRelDiscrete 7 := fun h => by
  have := congrArg View.frag ((@h Unit (Option (Excl TN)) _ _ (vRel _) _ _ _).discrete_0
    (x := ⟨none, some (.excl ⟨1⟩)⟩) (y := ⟨none, some (.excl ⟨2⟩)⟩) ⟨OFE.Dist.rfl, tn12⟩)
  simp at this

-- `View.instDiscreteOfDiscreteOfIsViewRelDiscrete` idx 8: necessary (A = NA, R n a _ := n = 0 or a = NA.a: ●V e valid at 0 only)
theorem w3c4_55 : ¬ drop0% View.instDiscreteOfDiscreteOfIsViewRelDiscrete 8 := fun h => by
  have hd := @h NA Unit _ _ zRel _ _ _
  have h0 : ✓{0} (●V NA.e : View zRel) := (View.auth_one_validN_iff 0 NA.e).mpr (.inl rfl)
  have h1 := (View.auth_one_valid_iff.mp (hd.discrete_valid h0)) 1
  rcases h1 with h | h <;> exact nomatch h

-- `View.isOp_view_auth_dfrac` idx 11: necessary (dq = own 1, dq1 = dq2 = discard)
theorem w3c4_58 : ¬ drop0% View.isOp_view_auth_dfrac 11 := fun h => by
  have := (@h Unit Unit _ _ (vRel Unit) _ .merge (.own 1) .discard .discard ()).is_op
  rw [← View.auth_op_auth_eqv] at this
  have := (View.auth_eqv_inj this).1
  first | exact nomatch this | cases this | simp at this

-- `View.instIsOpFrag` idx 10: necessary (B = NA, b = e, b1 = b2 = a)
theorem w3c4_69 : ¬ drop0% View.instIsOpFrag 10 := fun h => by
  have := congrArg View.frag (@h Unit NA _ _ (vRel NA) _ .merge .e .a .a).is_op
  exact nomatch (this : NA.e = NA.a)

-- `View.auth_one_op_frag_updateP` idx 9: necessary (A = B = Unit, all valid, Pab = False)
theorem w3c4_110 : ¬ drop0% View.auth_one_op_frag_updateP 9 := fun h => by
  obtain ⟨_, ⟨_, _, _, hp⟩, _⟩ := @h Unit Unit _ _ (vRel Unit) _ () () (fun _ _ => False) 0 none
    (by exact View.auth_one_op_frag_validN_iff.mpr trivial)
  exact hp

-- `View.auth_one_op_frag_update` idx 10: necessary (A = NA, R _ a _ := a = NA.a; a = a, a' = e)
theorem w3c4_112 : ¬ drop0% View.auth_one_op_frag_update 10 := fun h => by
  have := @h NA Unit _ _ aRel _ .a () .e () 0 none (by exact View.auth_one_op_frag_validN_iff.mpr rfl)
  exact nomatch (View.auth_one_op_frag_validN_iff.mp this : NA.e = NA.a)

-- `View.auth_one_alloc` idx 9: necessary (A = NA, R _ a _ := a = NA.a; a = a, a' = e)
theorem w3c4_114 : ¬ drop0% View.auth_one_alloc 9 := fun h => by
  have := @h NA Unit _ _ aRel _ .a .e () 0 none (by exact (View.auth_one_validN_iff 0 NA.a).mpr rfl)
  exact nomatch (View.auth_one_op_frag_validN_iff.mp this : NA.e = NA.a)

-- `View.auth_one_op_frag_dealloc` idx 9: necessary (A = NA, R _ a _ := a = NA.a; a = a, a' = e)
theorem w3c4_116 : ¬ drop0% View.auth_one_op_frag_dealloc 9 := fun h => by
  have := @h NA Unit _ _ aRel _ .a () .e 0 none (by exact View.auth_one_op_frag_validN_iff.mpr rfl)
  exact nomatch ((View.auth_one_validN_iff 0 NA.e).mp this : NA.e = NA.a)

-- `View.auth_one_update` idx 8: necessary (A = NA, R _ a _ := a = NA.a; a = a, a' = e)
theorem w3c4_118 : ¬ drop0% View.auth_one_update 8 := fun h => by
  have := @h NA Unit _ _ aRel _ .a .e 0 none (by exact (View.auth_one_validN_iff 0 NA.a).mpr rfl)
  exact nomatch ((View.auth_one_validN_iff 0 NA.e).mp this : NA.e = NA.a)

-- `View.auth_updateP` idx 9: necessary (A = B = Unit, all valid, P = False, dq = own 1)
theorem w3c4_120 : ¬ drop0% View.auth_updateP 9 := fun h => by
  obtain ⟨_, ⟨_, _, hp⟩, _⟩ := @h Unit Unit _ _ (vRel Unit) _ (.own 1) (fun _ => False) () 0 none
    (by exact (View.auth_one_validN_iff 0 ()).mpr trivial)
  exact hp

-- `View.frag_updateP` idx 8: necessary (A = B = Unit, all valid, P = False)
theorem w3c4_124 : ¬ drop0% View.frag_updateP 8 := fun h => by
  obtain ⟨_, ⟨_, _, hp⟩, _⟩ := @h Unit Unit _ _ (vRel Unit) _ () (fun _ => False) 0 none
    (by exact View.frag_validN_iff.mpr ⟨(), trivial⟩)
  exact hp

-- `View.frag_update` idx 8: necessary (validity relation on TX, b = e, b' = z)
theorem w3c4_126 : ¬ drop0% View.frag_update 8 := fun h => by
  have := @h Unit TX _ _ (vRel TX) _ .e .z 0 none (by exact View.frag_validN_iff.mpr ⟨(), tx_e_val 0⟩)
  obtain ⟨_, h2⟩ := View.frag_validN_iff.mp this
  exact tx_z_inv 0 h2

-- `View.auth_alloc` idx 9: necessary (validity relation on TX, dq = own 1, b = z)
theorem w3c4_128 : ¬ drop0% View.auth_alloc 9 := fun h => by
  have := @h Unit TX _ _ (vRel TX) _ () .z (.own 1) 0 none (by exact (View.auth_one_validN_iff 0 ()).mpr (tx_e_val 0))
  exact tx_z_inv 0 (View.auth_one_op_frag_validN_iff.mp this)

-- `View.view_local_update` idx 13: necessary (A = NA, R _ a _ := a = NA.a; a = a, a' = e, identity local update on Unit)
theorem w3c4_130 : ¬ drop0% View.view_local_update 13 := fun h => by
  have := (@h NA Unit _ _ aRel _ .a .e () () () () (LocalUpdate.id _) 0 none
    (by exact View.auth_one_op_frag_validN_iff.mpr rfl) OFE.Dist.rfl).1
  exact nomatch (View.auth_one_op_frag_validN_iff.mp this : NA.e = NA.a)

-- `View.map_ne` idx 15: removable (the proof only needs pointwise f1 a =n= f2 a for Agree.map')
theorem w3c4_131 : drop% View.map_ne 15 := by
  intro A B A' B' _ _ _ R R' n f1 f2 g1 g2 _ v h1 h2
  refine ⟨?_, h2 _⟩
  simp only [View.map]
  split
  · rfl
  · refine ⟨rfl, ?_⟩
    rename_i a _
    exact a.ind fun _ => by
      refine Agree.dist_mk.mpr ⟨?_, ?_⟩ <;> simp only [Agree.Raw.map'_car, List.mem_map] <;> rintro _ ⟨a, ha, rfl⟩
      · exact ⟨f2 a, ⟨a, ha, rfl⟩, h1 a⟩
      · exact ⟨f1 a, ⟨a, ha, rfl⟩, h1 a⟩

-- `View.map_ne` idx 17: necessary (A' = NA, f1 = const e, f2 = const a, v = ●V{own 1} ())
theorem w3c4_132 : ¬ drop0% View.map_ne 17 := fun h => by
  have := (@h Unit Unit NA Unit _ _ _ (fun _ _ _ => True) (fun _ _ _ => True) 0 (fun _ => .e) (fun _ => .a) id id
    ⟨fun _ _ _ _ => OFE.Dist.rfl⟩ ⟨fun _ _ _ _ => OFE.Dist.rfl⟩ ⟨some (.own 1, toAgree ()), ()⟩ (fun _ => OFE.Dist.rfl)).1
  have h2 : toAgree NA.e ≡{0}≡ toAgree NA.a := (some_dist_some.mp this).2
  exact nomatch (toAgree.inj h2 : NA.e = NA.a)

-- `View.instNonExpansiveMap` idx 12: necessary (A = A' = TN, f = bad (1 ↦ 0, 2 ↦ 1) not non-expansive)
theorem w3c4_133 : ¬ drop0% View.instNonExpansiveMap 12 := fun h => by
  have := ((@h TN Unit TN Unit _ _ _ _ tRel (fun _ _ _ => True) bad id _).ne (auth12 (R := tRel) ())).1
  have h2 : toAgree (bad ⟨1⟩) ≡{0}≡ toAgree (bad ⟨2⟩) := (some_dist_some.mp this).2
  exact bad12 (toAgree.inj h2)

-- `View.instNonExpansiveMap` idx 13: necessary (B = B' = TN, g = bad not non-expansive, fragments 1 and 2)
theorem w3c4_134 : ¬ drop0% View.instNonExpansiveMap 13 := fun h => by
  have := ((@h Unit TN Unit TN _ _ _ _ (fun _ _ _ => True) (fun _ _ _ => True) id bad _).ne
    (x₁ := ⟨none, ⟨1⟩⟩) (x₂ := ⟨none, ⟨2⟩⟩) ⟨OFE.Dist.rfl, tn12⟩).2
  exact bad12 this

-- `View.instIncOrd` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_43 : ¬ indep0% View.instIncOrd 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel))

-- `View.instOrdInc` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_45 : ¬ indep0% View.instOrdInc 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel))

-- `View.instIsInc` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_47 : ¬ indep0% View.instIsInc 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel))

-- `View.increasing_authElem` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_49 : ¬ indep0% View.increasing_authElem 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (dq := Iris.DFrac.discard) (a := ()))

-- `View.increasing_fragElem` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_50 : ¬ indep0% View.increasing_fragElem 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (b := ()))

-- `View.auth_op_auth_eqv` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_56 : ¬ indep0% View.auth_op_auth_eqv 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (dq1 := Iris.DFrac.discard) (dq2 := Iris.DFrac.discard) (a := ()))

-- `View.isOp_view_auth_dfrac` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_57 : ¬ indep0% View.isOp_view_auth_dfrac 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (d := .merge) (dq := (Iris.DFrac.discard • Iris.DFrac.discard)) (dq1 := Iris.DFrac.discard) (dq2 := Iris.DFrac.discard) (a := ()))

-- `View.frag_op_eq` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_59 : ¬ indep0% View.frag_op_eq 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (b1 := ()) (b2 := ()))

-- `View.frag_ord_of_ord` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_60 : ¬ indep0% View.frag_ord_of_ord 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (b1 := ()) (b2 := ()) (by first | trivial | exact OrderRefl.ord_refl ()))

-- `View.frag_inc_of_inc` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_61 : ¬ indep0% View.frag_inc_of_inc 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (b1 := ()) (b2 := ()) (ORA.inc_refl _))

-- `View.frag_core` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_62 : ¬ indep0% View.frag_core 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (b := ()))

-- `View.auth_discard_op_frag_core` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_63 : ¬ indep0% View.auth_discard_op_frag_core 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (a := ()) (b := ()))

-- `View.auth_own_op_frag_core` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_64 : ¬ indep0% View.auth_own_op_frag_core 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (q := 1) (a := ()) (b := ()))

-- `View.instCoreIdAuthDiscard` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_65 : ¬ indep0% View.instCoreIdAuthDiscard 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (a := ()))

-- `View.instCoreIdFrag` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_66 : ¬ indep0% View.instCoreIdFrag 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (b := ()))

-- `View.instCoreIdOpAuthDiscardFrag` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_67 : ¬ indep0% View.instCoreIdOpAuthDiscardFrag 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (b := ()) (a := ()))

-- `View.instIsOpFrag` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_68 : ¬ indep0% View.instIsOpFrag 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (d := .merge) (b := (() • ())) (b1 := ()) (b2 := ()))

-- `View.instMonoidHomomorphismOpUnitEqFrag` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_70 : ¬ indep0% View.instMonoidHomomorphismOpUnitEqFrag 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel))

-- `View.bigOpM_frag` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_71 : ¬ indep0% View.bigOpM_frag 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (M' := TM) (K := Nat) (C := Nat) (g := (fun _ _ => ())) (m := ∅))

-- `View.bigOpS_frag` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_72 : ¬ indep0% View.bigOpS_frag 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (S' := TS) (C := Nat) (g := (fun _ => ())) (X := ∅))

-- `View.bigOpMS_frag` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_73 : ¬ indep0% View.bigOpMS_frag 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (MS' := MSN) (C := Nat) (g := (fun _ => ())) (X := ∅))

-- `View.dist_of_validN_auth` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_74 : ¬ indep0% View.dist_of_validN_auth 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (n := 0) (dq1 := Iris.DFrac.discard) (a1 := ()) (dq2 := Iris.DFrac.discard) (a2 := ()))

-- `View.eq_of_valid_auth` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_75 : ¬ indep0% View.eq_of_valid_auth 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (dq1 := Iris.DFrac.discard) (a1 := ()) (dq2 := Iris.DFrac.discard) (a2 := ()))

-- `View.auth_validN_iff` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_76 : ¬ indep0% View.auth_validN_iff 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (n := 0) (dq := Iris.DFrac.discard) (a := ()))

-- `View.auth_one_validN_iff` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_77 : ¬ indep0% View.auth_one_validN_iff 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (n := 0) (a := ()))

-- `View.auth_op_auth_validN_iff` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_78 : ¬ indep0% View.auth_op_auth_validN_iff 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (n := 0) (dq1 := Iris.DFrac.discard) (a1 := ()) (dq2 := Iris.DFrac.discard) (a2 := ()))

-- `View.auth_one_op_auth_one_validN_iff` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_79 : ¬ indep0% View.auth_one_op_auth_one_validN_iff 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (n := 0) (a1 := ()) (a2 := ()))

-- `View.frag_validN_iff` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_80 : ¬ indep0% View.frag_validN_iff 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (n := 0) (b := ()))

-- `View.auth_op_frag_validN_iff` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_81 : ¬ indep0% View.auth_op_frag_validN_iff 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (n := 0) (dq := Iris.DFrac.discard) (a := ()) (b := ()))

-- `View.auth_one_op_frag_validN_iff` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_82 : ¬ indep0% View.auth_one_op_frag_validN_iff 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (n := 0) (a := ()) (b := ()))

-- `View.auth_valid_iff` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_83 : ¬ indep0% View.auth_valid_iff 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (dq := Iris.DFrac.discard) (a := ()))

-- `View.auth_one_valid_iff` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_84 : ¬ indep0% View.auth_one_valid_iff 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (a := ()))

-- `View.auth_op_auth_valid_iff` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_85 : ¬ indep0% View.auth_op_auth_valid_iff 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (dq1 := Iris.DFrac.discard) (a1 := ()) (dq2 := Iris.DFrac.discard) (a2 := ()))

-- `View.auth_one_op_auth_one_valid_iff` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_86 : ¬ indep0% View.auth_one_op_auth_one_valid_iff 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (a1 := ()) (a2 := ()))

-- `View.frag_valid_iff` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_87 : ¬ indep0% View.frag_valid_iff 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (b := ()))

-- `View.auth_op_frag_valid_iff` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_88 : ¬ indep0% View.auth_op_frag_valid_iff 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (dq := Iris.DFrac.discard) (a := ()) (b := ()))

-- `View.auth_one_op_frag_valid_iff` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_89 : ¬ indep0% View.auth_one_op_frag_valid_iff 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (a := ()) (b := ()))

-- `View.auth_incN_auth_op_frag_iff` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_90 : ¬ indep0% View.auth_incN_auth_op_frag_iff 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (n := 0) (dq1 := Iris.DFrac.discard) (a1 := ()) (dq2 := Iris.DFrac.discard) (a2 := ()) (b := ()))

-- `View.auth_inc_auth_op_frag_iff` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_91 : ¬ indep0% View.auth_inc_auth_op_frag_iff 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (dq1 := Iris.DFrac.discard) (a1 := ()) (dq2 := Iris.DFrac.discard) (a2 := ()) (b := ()))

-- `View.auth_one_incN_auth_one_op_frag_iff` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_92 : ¬ indep0% View.auth_one_incN_auth_one_op_frag_iff 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (n := 0) (a1 := ()) (a2 := ()) (b := ()))

-- `View.auth_one_inc_auth_one_op_frag_iff` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_93 : ¬ indep0% View.auth_one_inc_auth_one_op_frag_iff 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (a1 := ()) (a2 := ()) (b := ()))

-- `View.frag_inc_auth_op_frag_iff` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_94 : ¬ indep0% View.frag_inc_auth_op_frag_iff 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (b1 := ()) (p := Iris.DFrac.discard) (a := ()) (b2 := ()))

-- `View.auth_op_frag_incN_auth_op_frag_iff` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_95 : ¬ indep0% View.auth_op_frag_incN_auth_op_frag_iff 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (n := 0) (dq1 := Iris.DFrac.discard) (a1 := ()) (b1 := ()) (dq2 := Iris.DFrac.discard) (a2 := ()) (b2 := ()))

-- `View.auth_op_frag_inc_auth_op_frag_iff` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_96 : ¬ indep0% View.auth_op_frag_inc_auth_op_frag_iff 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (dq1 := Iris.DFrac.discard) (a1 := ()) (b1 := ()) (dq2 := Iris.DFrac.discard) (a2 := ()) (b2 := ()))

-- `View.auth_one_op_frag_incN_auth_one_op_frag_iff` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_97 : ¬ indep0% View.auth_one_op_frag_incN_auth_one_op_frag_iff 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (n := 0) (a1 := ()) (b1 := ()) (a2 := ()) (b2 := ()))

-- `View.auth_one_op_frag_inc_auth_one_op_frag_iff` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_98 : ¬ indep0% View.auth_one_op_frag_inc_auth_one_op_frag_iff 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (a1 := ()) (b1 := ()) (a2 := ()) (b2 := ()))

-- `View.auth_ordN_auth_op_frag_iff` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_99 : ¬ indep0% View.auth_ordN_auth_op_frag_iff 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (b := ()) (n := 0) (dq1 := Iris.DFrac.discard) (a1 := ()) (dq2 := Iris.DFrac.discard) (a2 := ()))

-- `View.auth_ord_auth_op_frag_iff` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_100 : ¬ indep0% View.auth_ord_auth_op_frag_iff 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (b := ()) (dq1 := Iris.DFrac.discard) (a1 := ()) (dq2 := Iris.DFrac.discard) (a2 := ()))

-- `View.auth_one_ordN_auth_one_op_frag_iff` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_101 : ¬ indep0% View.auth_one_ordN_auth_one_op_frag_iff 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (b := ()) (n := 0) (a1 := ()) (a2 := ()))

-- `View.auth_one_ord_auth_one_op_frag_iff` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_102 : ¬ indep0% View.auth_one_ord_auth_one_op_frag_iff 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (b := ()) (a1 := ()) (a2 := ()))

-- `View.frag_ordN_auth_op_frag_iff` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_103 : ¬ indep0% View.frag_ordN_auth_op_frag_iff 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (n := 0) (b1 := ()) (p := Iris.DFrac.discard) (a := ()) (b2 := ()))

-- `View.frag_ord_auth_op_frag_iff` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_104 : ¬ indep0% View.frag_ord_auth_op_frag_iff 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (b1 := ()) (p := Iris.DFrac.discard) (a := ()) (b2 := ()))

-- `View.auth_op_frag_ordN_auth_op_frag_iff` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_105 : ¬ indep0% View.auth_op_frag_ordN_auth_op_frag_iff 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (n := 0) (dq1 := Iris.DFrac.discard) (a1 := ()) (b1 := ()) (dq2 := Iris.DFrac.discard) (a2 := ()) (b2 := ()))

-- `View.auth_op_frag_ord_auth_op_frag_iff` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_106 : ¬ indep0% View.auth_op_frag_ord_auth_op_frag_iff 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (dq1 := Iris.DFrac.discard) (a1 := ()) (b1 := ()) (dq2 := Iris.DFrac.discard) (a2 := ()) (b2 := ()))

-- `View.auth_one_op_frag_ord_auth_one_op_frag_iff` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_107 : ¬ indep0% View.auth_one_op_frag_ord_auth_one_op_frag_iff 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (a1 := ()) (b1 := ()) (a2 := ()) (b2 := ()))

-- `View.auth_one_op_frag_ordN_auth_one_op_frag_iff` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_108 : ¬ indep0% View.auth_one_op_frag_ordN_auth_one_op_frag_iff 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (n := 0) (a1 := ()) (b1 := ()) (a2 := ()) (b2 := ()))

-- `View.auth_one_op_frag_updateP` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_109 : ¬ indep0% View.auth_one_op_frag_updateP 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (a := ()) (b := ()) (Pab := (fun _ _ => True)) (by intros; rename_i hr; exact hr.elim))

-- `View.auth_one_op_frag_update` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_111 : ¬ indep0% View.auth_one_op_frag_update 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (a := ()) (b := ()) (a' := ()) (b' := ()) (by intros; rename_i hr; exact hr.elim))

-- `View.auth_one_alloc` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_113 : ¬ indep0% View.auth_one_alloc 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (a := ()) (a' := ()) (b' := ()) (by intros; rename_i hr; exact hr.elim))

-- `View.auth_one_op_frag_dealloc` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_115 : ¬ indep0% View.auth_one_op_frag_dealloc 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (a := ()) (b := ()) (a' := ()) (by intros; rename_i hr; exact hr.elim))

-- `View.auth_one_update` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_117 : ¬ indep0% View.auth_one_update 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (a := ()) (a' := ()) (by intros; rename_i hr; exact hr.elim))

-- `View.auth_updateP` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_119 : ¬ indep0% View.auth_updateP 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (dq := Iris.DFrac.discard) (P := (fun _ => True)) (a := ()) (fun _ _ hv => ⟨_, trivial, hv⟩))

-- `View.auth_acquire` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_121 : ¬ indep0% View.auth_acquire 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (a := ()))

-- `View.auth_op_frag_acquire` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_122 : ¬ indep0% View.auth_op_frag_acquire 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (a := ()) (b := ()))

-- `View.frag_updateP` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_123 : ¬ indep0% View.frag_updateP 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (b := ()) (P := (fun _ => True)) (by intros; rename_i hr; exact hr.elim))

-- `View.frag_update` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_125 : ¬ indep0% View.frag_update 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (b := ()) (b' := ()) (by intros; rename_i hr; exact hr.elim))

-- `View.auth_alloc` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_127 : ¬ indep0% View.auth_alloc 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (a := ()) (b := ()) (dq := Iris.DFrac.discard) (by intros; rename_i hr; exact hr.elim))

-- `View.view_local_update` idx 5: necessary (A = B = Unit, R = empty relation: no unit, not a view relation)
theorem w3c4_129 : ¬ indep0% View.view_local_update 5 := fun h =>
  noVR (h (A := Unit) (B := Unit) (R := fRel) (a := ()) (a' := ()) (b0 := ()) (b1 := ()) (b0' := ()) (b1' := ()) (LocalUpdate.id _) (by intros; rename_i hr; exact hr.elim))

