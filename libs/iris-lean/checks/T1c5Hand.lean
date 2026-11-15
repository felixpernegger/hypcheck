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
namespace T1c5
open Iris Iris.OFE

/-- f tends to infinity. -/
def Tinf (f : Nat → Nat) : Prop := ∀ M, ∃ N, ∀ i, N ≤ i → M ≤ f i

/-- Sequences of naturals that are zero or tend to infinity; n-distance = agreement up to n. -/
structure SQ where
  f : Nat → Nat
  ok : (∀ i, f i = 0) ∨ Tinf f

theorem SQ.ext' {x y : SQ} (h : ∀ i, x.f i = y.f i) : x = y := by
  cases x; cases y; simp only [SQ.mk.injEq]; funext i; exact h i

instance : OFE SQ where
  Dist n x y := ∀ i, i ≤ n → x.f i = y.f i
  dist_eqv := ⟨fun _ _ _ => rfl, fun h i hi => (h i hi).symm, fun h1 h2 i hi => (h1 i hi).trans (h2 i hi)⟩
  eq_dist' := ⟨fun h _ _ _ => h ▸ rfl, fun h => SQ.ext' fun i => h i i (Nat.le_refl _)⟩
  dist_lt h hm i hi := h i (by omega)

theorem sq_dist {n} {x y : SQ} : x ≡{n}≡ y ↔ ∀ i, i ≤ n → x.f i = y.f i := Iff.rfl

theorem tinf_le {f g : Nat → Nat} (h : Tinf f) (hle : ∀ i, f i ≤ g i) : Tinf g := fun M =>
  let ⟨N, hN⟩ := h M; ⟨N, fun i hi => Nat.le_trans (hN i hi) (hle i)⟩

def SQ.add (x y : SQ) : SQ := ⟨fun i => x.f i + y.f i, by
  rcases x with ⟨f, hf | hf⟩ <;> rcases y with ⟨g, hg | hg⟩
  · exact .inl fun i => by simp only [hf i, hg i]
  · exact .inr (tinf_le hg fun i => Nat.le_add_left _ _)
  · exact .inr (tinf_le hf fun i => Nat.le_add_right _ _)
  · exact .inr (tinf_le hf fun i => Nat.le_add_right _ _)⟩

def zero : SQ := ⟨fun _ => 0, .inl fun _ => rfl⟩

instance : Op SQ where
  op := SQ.add
  op_ne := ⟨fun n y z h i hi => by show _ + _ = _ + _; rw [h i hi]⟩
  assoc := SQ.ext' fun i => (Nat.add_assoc _ _ _).symm
  comm := SQ.ext' fun i => Nat.add_comm _ _

@[simp] theorem op_f (x y : SQ) (i : Nat) : (x • y).f i = x.f i + y.f i := rfl
@[simp] theorem zero_f (i : Nat) : zero.f i = 0 := rfl

instance : PCore SQ where
  pcore _ := some zero
  pcore_ne _ h := ⟨zero, rfl, by cases h; exact Dist.rfl⟩
  pcore_idem h := by cases h; rfl

instance : Valid SQ where
  ValidN _ _ := True
  Valid _ := True
  validN_ne _ h := h
  valid_iff_validN := ⟨fun _ _ => trivial, fun _ => trivial⟩
  validN_succ h := h

instance : Ordered SQ where
  OrderN n x y := ∃ z, y ≡{n}≡ x • z
  Order x y := ∃ z, y = x • z
  ordN_ne ex ey := fun ⟨z, hz⟩ => ⟨z, ey.symm.trans (hz.trans ex.op_l)⟩
  ordN_succ := fun ⟨z, hz⟩ => ⟨z, hz.lt (Nat.lt_succ_self _)⟩
  ordN_trans := fun ⟨z1, h1⟩ ⟨z2, h2⟩ => ⟨z1 • z2, h2.trans (h1.op_l.trans (Dist.of_eq Op.assoc.symm))⟩
  ord_trans := fun ⟨z1, h1⟩ ⟨z2, h2⟩ => ⟨z1 • z2, by subst h1; subst h2; exact Op.assoc.symm⟩
  ordN_of_ord _ := fun ⟨z, h⟩ => ⟨z, Dist.of_eq h⟩

theorem mk_ok (x : SQ) (n : Nat) (g : Nat → Nat) (h0 : ∀ i, i ≤ n → g i ≤ x.f i)
    (h1 : ∀ i, n < i → x.f i / 2 ≤ g i ∧ g i ≤ x.f i) : (∀ i, g i = 0) ∨ Tinf g := by
  rcases x.ok with hx | hx
  · refine .inl fun i => ?_
    by_cases hi : i ≤ n
    · have := h0 i hi; have := hx i; omega
    · have := h1 i (by omega); have := hx i; omega
  · refine .inr fun M => ?_
    obtain ⟨N, hN⟩ := hx (2 * M)
    exact ⟨N + n + 1, fun i hi => by have := hN i (by omega); have := h1 i (by omega); omega⟩

def sqExtend {n} {x y₁ y₂ : SQ} (h : x ≡{n}≡ y₁ • y₂) :
    Σ' z₁ z₂ : SQ, x = z₁ • z₂ ∧ z₁ ≡{n}≡ y₁ ∧ z₂ ≡{n}≡ y₂ :=
  ⟨⟨fun i => if i ≤ n then y₁.f i else x.f i / 2, mk_ok x n _
      (fun i hi => by have := h i hi; simp only [op_f] at this; simp only [hi, ite_true]; omega)
      (fun i hi => by simp only [show ¬ i ≤ n by omega, ite_false]; omega)⟩,
   ⟨fun i => if i ≤ n then y₂.f i else x.f i - x.f i / 2, mk_ok x n _
      (fun i hi => by have := h i hi; simp only [op_f] at this; simp only [hi, ite_true]; omega)
      (fun i hi => by simp only [show ¬ i ≤ n by omega, ite_false]; omega)⟩,
   SQ.ext' fun i => by
      by_cases hi : i ≤ n
      · have := h i hi; simp only [op_f] at this ⊢; simp only [hi, ite_true]; omega
      · simp only [op_f, hi, ite_false]; omega,
   fun i hi => by simp only [hi, ite_true],
   fun i hi => by simp only [hi, ite_true]⟩

theorem incr (x : SQ) : Increasing x := ⟨fun y => ⟨x, Op.comm⟩⟩

instance sqORA : ORA SQ where
  validN_op_left _ := trivial
  pcore_op_left h := by cases h; exact SQ.ext' fun i => Nat.zero_add _
  extend _ h := sqExtend h
  op_monoN_left_ord z := fun ⟨w, hw⟩ => ⟨w, fun i hi => by have := hw i hi; simp only [op_f] at this ⊢; omega⟩
  op_mono_left_ord z := fun ⟨w, hw⟩ => ⟨w, by subst hw; exact SQ.ext' fun i => by simp only [op_f]; omega⟩
  validN_of_ordN _ _ := trivial
  pcore_monoN_ord _ h := ⟨zero, rfl, by cases h; exact ⟨zero, Dist.of_eq (SQ.ext' fun _ => rfl)⟩⟩
  pcore_mono_ord _ h := ⟨zero, rfl, by cases h; exact ⟨zero, SQ.ext' fun _ => rfl⟩⟩
  pcore_order_op h _ := ⟨zero, rfl, by cases h; exact ⟨zero, SQ.ext' fun _ => rfl⟩⟩
  pcore_increasing _ := incr _
  increasing_closed _ _ := incr _
  ordN_extend _ := fun ⟨_, hc⟩ =>
    let ⟨z1, z2, e, d1, _⟩ := sqExtend hc
    ⟨z1, ⟨z2, Dist.of_eq e⟩, d1⟩

instance sqUORA : UORA SQ where
  ord_refl x := ⟨zero, SQ.ext' fun i => (Nat.add_zero _).symm⟩
  unit := zero
  unit_valid := trivial
  unit_left_id := SQ.ext' fun i => Nat.zero_add _
  pcore_unit := rfl

instance sqOrdInc : OrdInc SQ := ⟨fun h => h, fun h => h⟩

/-- b i = i. -/
def sb : SQ := ⟨fun i => i, .inr fun M => ⟨M, fun _ hi => hi⟩⟩
/-- a = b plus one at index 0. -/
def sa : SQ := ⟨fun i => i + (if i = 0 then 1 else 0), .inr fun M => ⟨M, fun i hi => by dsimp only; split <;> omega⟩⟩
/-- Frame for step n: 1 at index 0, 0 up to n, then i. -/
def zn (n : Nat) : SQ := ⟨fun i => if i = 0 then 1 else if i ≤ n then 0 else i,
  .inr fun M => ⟨M + n + 1, fun i hi => by dsimp only; split <;> (try split) <;> omega⟩⟩

theorem sa_dist (n : Nat) : sa ≡{n}≡ sb • zn n := fun i hi => by
  simp only [op_f, sa, sb, zn]; split <;> (try split) <;> omega

theorem sb_not_inc : ¬ sb ≼ sa := fun ⟨z, hz⟩ => by
  have h0 := congrArg (fun x => SQ.f x 0) hz
  simp only [op_f, sa, sb] at h0
  rcases z.ok with hz0 | hzi
  · have := hz0 0; simp at h0; omega
  · obtain ⟨N, hN⟩ := hzi 1
    have h1 := congrArg (fun x => SQ.f x (N + 1)) hz
    simp only [op_f, sa, sb] at h1
    have := hN (N + 1) (by omega)
    split at h1 <;> omega

end T1c5
namespace T1c5
open Iris Iris.OFE Iris.ORA


theorem sb_ne_sa : sb ≠ sa := fun e => by
  have := congrArg (fun x => SQ.f x 0) e; simp [sa, sb] at this

theorem not_some_inc : ¬ (some sb ≼ some sa) := fun h =>
  (Iris.Option.eq_or_inc_of_some_inc_some h).elim sb_ne_sa sb_not_inc

theorem sq_frame (n : Nat) : sb • zn n ≼ₒ{n} sa :=
  ⟨zero, fun i hi => by have := sa_dist n i hi; simp only [op_f, zero_f] at this ⊢; omega⟩

abbrev TM (V : Type) := Std.ExtTreeMap Nat V compare
abbrev sg {V : Type} (x : V) : TM V := Iris.Std.PartialMap.insert ∅ 0 x
theorem sg_get {V : Type} (x : V) : Iris.Std.get? (sg x) 0 = some x := Iris.Std.LawfulPartialMap.get?_insert_eq rfl
theorem q_sum : (Qp.quarter + Qp.threeQuarters : Qp) = 1 := Qp.quarter_add_threeQuarters

theorem hv_valid : ✓ (HeapView.Auth (DFrac.own 1) (sg sa) • HeapView.Frag 0 (DFrac.own Qp.quarter) sb : HeapView Nat SQ TM) :=
  valid_iff_validN.mpr fun n => HeapView.auth_op_frag_validN_iff_frame.mpr
    ⟨sa, DFrac.own 1, DFrac.valid_own_one, sg_get _, ⟨DFrac.valid_own_one, trivial⟩,
     some (DFrac.own Qp.threeQuarters, zn n), .inl ⟨congrArg DFrac.own q_sum, (sa_dist n).symm⟩⟩

end T1c5
open Iris Iris.OFE Iris.ORA T1c5

-- `Auth.both_dfrac_valid_discrete` idx 2: necessary (SQ: b = id, a = b + δ0; b ≼{n} a for all n, not b ≼ a)
theorem t1c5_1 : ¬ drop0% Auth.both_dfrac_valid_discrete 2 := fun h => by
  have v := (Auth.both_dfrac_valid_frame (A := SQ) (dq := DFrac.own 1) (a := sa) (b := sb)).mpr
    ⟨DFrac.valid_own_one, fun n => ⟨zn n, sq_frame n⟩, trivial⟩
  exact sb_not_inc ((@h SQ _ sqOrdInc _ _ _).mp v).2.1

-- `Auth.auth_both_valid_discrete` idx 2: necessary (same SQ model)
theorem t1c5_2 : ¬ drop0% Auth.auth_both_valid_discrete 2 := fun h => by
  have v := (Auth.auth_both_valid_frame (A := SQ) (a := sa) (b := sb)).mpr
    ⟨fun n => ⟨zn n, sq_frame n⟩, trivial⟩
  exact sb_not_inc ((@h SQ _ sqOrdInc _ _).mp v).1

-- `HeapView.auth_op_frag_discrete_valid_iff` idx 10: necessary (one-key heap 0 ↦ sa, fragment sb)
theorem t1c5_3 : ¬ drop0% HeapView.auth_op_frag_discrete_valid_iff 10 := fun h => by
  obtain ⟨v', dq', -, hg, -, hi⟩ := (@h Nat SQ TM _ _ (DFrac.own 1) (DFrac.own Qp.quarter) (sg sa) 0 sb sqOrdInc).mp hv_valid
  rw [sg_get] at hg; cases hg
  rcases Iris.Option.eq_or_inc_of_some_inc_some hi with e | ⟨z, hz⟩
  · exact sb_ne_sa (congrArg Prod.snd e)
  · exact sb_not_inc ⟨z.2, congrArg Prod.snd hz⟩

-- `HeapView.auth_op_frag_valid_total_discrete_iff` idx 11: necessary (same heap)
theorem t1c5_4 : ¬ drop0% HeapView.auth_op_frag_valid_total_discrete_iff 11 := fun h => by
  obtain ⟨v', -, -, hg, -, hi⟩ := @h Nat SQ TM _ _ (DFrac.own 1) (DFrac.own Qp.quarter) (sg sa) 0 sb _ sqOrdInc hv_valid
  rw [sg_get] at hg; cases hg
  exact sb_not_inc hi

-- `FracAuth.included` idx 3: necessary (SQ, fragment 1/4 with frame 3/4)
theorem t1c5_5 : ¬ drop0% FracAuth.included 3 := fun h => by
  have v := (Auth.both_dfrac_valid_frame (A := Option (Qp × SQ)) (dq := DFrac.own 1) (a := some (1, sa)) (b := some (Qp.quarter, sb))).mpr
    ⟨DFrac.valid_own_one, fun n => ⟨some (Qp.threeQuarters, zn n), .inl ⟨q_sum, (sa_dist n).symm⟩⟩,
     valid_iff_validN.mpr fun _ => ⟨Qp.valid_one, trivial⟩⟩
  exact not_some_inc (@h SQ _ Qp.quarter sqOrdInc (DFrac.own 1) sa sb v)

-- `FracAuth.included_total` idx 3: necessary (same)
theorem t1c5_6 : ¬ drop0% FracAuth.included_total 3 := fun h => by
  have v := (Auth.both_dfrac_valid_frame (A := Option (Qp × SQ)) (dq := DFrac.own 1) (a := some (1, sa)) (b := some (Qp.quarter, sb))).mpr
    ⟨DFrac.valid_own_one, fun n => ⟨some (Qp.threeQuarters, zn n), .inl ⟨q_sum, (sa_dist n).symm⟩⟩,
     valid_iff_validN.mpr fun _ => ⟨Qp.valid_one, trivial⟩⟩
  exact sb_not_inc (h (A := SQ) (q := Qp.quarter) (dq := DFrac.own 1) (a := sa) (b := sb) v)
namespace T1c5
open Iris Iris.OFE Iris.ORA Iris.UFracAuth
/-- Validity with an explicit frame c: the authoritative part is b • c with fraction q + r (from W2c4). -/
theorem uf_valid_frame {A : Type} [ORA A] {n : Nat} (q r : Qp) (b c : A) (hv : ✓{n} (b • c)) :
    ✓{n} ((●U{q + r} (b • c)) • ◯U{q} b) :=
  Auth.both_validN_frame.mpr ⟨⟨some (⟨r⟩, c), .inl OFE.Dist.rfl⟩, ⟨trivial, hv⟩⟩

theorem uf_v : ✓ ((●U{Qp.quarter + Qp.threeQuarters} sa) • ◯U{Qp.quarter} sb : UFracAuth (A := SQ)) :=
  valid_iff_validN.mpr fun n =>
    validN_ne (UFracAuth.auth_ne.ne (sa_dist n).symm).op_l (uf_valid_frame _ _ sb (zn n) trivial)
end T1c5
open Iris Iris.OFE Iris.ORA T1c5

-- `Iris.UFracAuth.included` idx 2: necessary (SQ model, fractions 1/4 and 3/4)
theorem t1c5_7 : ¬ drop0% Iris.UFracAuth.included 2 := fun h =>
  not_some_inc (@h SQ _ sqOrdInc _ _ _ _ uf_v)

-- `Iris.UFracAuth.included_total` idx 2: necessary (same)
theorem t1c5_8 : ¬ drop0% Iris.UFracAuth.included_total 2 := fun h =>
  sb_not_inc (@h SQ _ _ sqOrdInc _ _ _ _ uf_v)
namespace T1c5
open Iris Iris.BI
set_option linter.constructorNameAsVariable false

/-- e unit, x ≤ y, e ≤ y, all other products y, all valid, core e: not IncOrd (x not increasing). -/
inductive XY | e | x | y deriving DecidableEq

def XY.op : XY → XY → XY
  | .e, b => b
  | a, .e => a
  | _, _ => .y

instance : OFE XY := OFE.ofDiscrete XY
instance : OFE.Discrete XY := ⟨id⟩

instance instORAXY : ORA XY := ORA.ofDiscreteORAData {
  pcore := fun _ => some .e
  op := XY.op
  Valid := fun _ => True
  Order := fun a b => a = b ∨ b = .y
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
  pcore_op_left := by intro x cx h; cases h; cases x <;> rfl
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := fun _ _ _ => trivial
  ord_trans := by intro x y z h1 h2; cases x <;> cases y <;> cases z <;> simp_all
  op_mono_left := by intro x y z h; cases x <;> cases y <;> cases z <;> simp_all [XY.op]
  valid_of_ord := fun _ _ _ _ => trivial
  pcore_mono := by intro x y cx h1 h2; exact ⟨.e, rfl, by cases h2; exact .inl rfl⟩
  pcore_order_op := by intro x cx h y; exact ⟨.e, rfl, by cases h; exact .inl rfl⟩
  pcore_increasing := by intro x cx h y; cases h; exact .inl rfl
  increasing_closed := by
    intro a b ha hab z; have h1 := ha .e
    cases a <;> cases b <;> cases z <;> simp_all [XY.op] }

instance : OrderRefl XY := ⟨fun x => show x = x ∨ x = .y from .inl rfl⟩

instance instUORAXY : UORA XY where
  unit := .e
  unit_valid := trivial
  unit_left_id := rfl
  pcore_unit := rfl

abbrev vxy (n : Nat) (a : XY) : ValidAt XY n := ⟨a, trivial⟩

abbrev S0 : UPred XY := UPred.ownM XY.x
abbrev P0 : UPred XY := iprop(False)
abbrev Q0 : UPred XY := iprop(▷ False)

/-- View shift: intuitionistic implication, or (target P0 and S), or (S and emp). Transitive, contains □(P → Q). -/
def vsX : CoPset → CoPset → UPred XY → UPred XY → UPred XY := fun _ _ P Q =>
  iprop(□ (P → Q) ∨ (⌜Q = P0⌝ ∧ S0) ∨ (S0 ∧ emp))

theorem vsX_impl : ∀ E P Q, iprop(□ (P → Q)) ⊢ vsX E E P Q := fun _ _ _ _ _ h => Or.inl h

theorem vsX_trans : ∀ E1 E2 E3 P Q R, iprop(vsX E1 E2 P Q ∧ vsX E2 E3 Q R) ⊢ vsX E1 E3 P R := by
  intro _ _ _ P Q R n w ⟨h1, h2⟩
  rcases h1 with ⟨he1, hi1⟩ | ⟨hq, hs⟩ | ⟨hs, he⟩ <;>
    rcases h2 with ⟨he2, hi2⟩ | ⟨hr, hs'⟩ | ⟨hs', he'⟩
  · exact Or.inl ⟨he1, fun x' hx hn hp => hi2 x' hx hn (hi1 x' hx hn hp)⟩
  · exact Or.inr (Or.inl ⟨hr, hs'⟩)
  · exact Or.inr (Or.inr ⟨hs', he'⟩)
  · exact Or.inr (Or.inr ⟨hs, he2⟩)
  · exact Or.inr (Or.inl ⟨hr, hs'⟩)
  · exact Or.inr (Or.inr ⟨hs', he'⟩)
  · exact Or.inr (Or.inr ⟨hs, he⟩)
  · exact Or.inr (Or.inr ⟨hs, he⟩)
  · exact Or.inr (Or.inr ⟨hs, he⟩)

theorem q0_ne : Q0 ≠ P0 := fun e => by
  have : Q0.holds 0 (vxy 0 .e) := trivial
  rw [e] at this; exact this

theorem fupdP0 : (fupd_vs vsX ∅ ∅ P0).holds 1 (vxy 1 .x) :=
  ⟨_, ⟨emp, rfl⟩, XY.e, XY.x, Or.inl rfl, Or.inl rfl, Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)⟩

theorem not_fupdQ0 : ¬ (fupd_vs vsX ∅ ∅ Q0).holds 1 (vxy 1 .x) := by
  rintro ⟨_, ⟨R, rfl⟩, x1, x2, hsp, hR, hvs⟩
  have hsp' : XY.op x1 x2 = .x ∨ XY.x = .y := hsp
  rcases hvs with ⟨he, hi⟩ | ⟨hq, _⟩ | ⟨hs, he⟩
  · have he' : XY.e = x2 ∨ x2 = .y := he
    cases x1 <;> cases x2 <;> simp [XY.op] at hsp' he'
    exact hi (vxy 1 .y) (Or.inr rfl) (Nat.le_refl 1) (R.mono hR (Or.inr rfl) (Nat.le_refl 1))
  · exact q0_ne hq
  · have he' : XY.e = x2 ∨ x2 = .y := he
    have hs' : XY.x = x2 ∨ x2 = .y := hs
    cases x1 <;> cases x2 <;> simp [XY.op] at hsp' he' hs'
end T1c5
open Iris Iris.BI T1c5

-- `Iris.fupd_vs_mono` idx 3: necessary (UPred XY, vs P Q = □(P → Q) ∨ (Q = False ∧ own x) ∨ (own x ∧ emp); fupd False holds at x, fupd ▷False does not)
theorem t1c5_9 : ¬ drop0% Iris.fupd_vs_mono 3 := fun h =>
  not_fupdQ0 ((@h XY _ vsX ∅ ∅ P0 Q0 (fun _ _ hf => hf.elim) vsX_trans vsX_impl) 1 (vxy 1 .x) fupdP0)
namespace T1c5
open Iris Iris.BI Iris.Std

noncomputable abbrev CGF := Iris.Examples.ClosedProofs.GF

theorem full_not_disj : ¬ (CoPset.full ## CoPset.full) := fun hd => hd .xH ⟨rfl, rfl⟩

/-- ⊢ |={⊤|}=> False under every invariant setup is unsound (from W7c0). -/
theorem ffin_false {GF : BundledGFunctors} [InvGpreS GF]
    (H : ∀ [InvGS_gen .hasNoLC GF], ⊢ (iprop(|={⊤|}=> ⌜False⌝) : IProp GF)) : False :=
  pure_soundness (PROP := IProp GF)
    (fupd_finally_soundness .hasNoLC 0 ⊤ iprop(⌜False⌝) fun _ => true_intro.trans (true_emp.mp.trans H))

/-- ⊢ |={⊤,∅}=> ownE ⊤ (from W6c1). -/
theorem own_open [InvGS_gen .hasNoLC CGF] : ⊢ (iprop(|={⊤,∅}=> ownE ⊤) : IProp CGF) := by
  refine .trans ?_ (fupd_unfold_no_lc ⊤ ∅ _).2
  iintro - ⟨Hw, HE⟩
  imod ownE_empty with H0
  imodintro
  iapply except0_intro
  isplitl [Hw]
  · iexact Hw
  isplitl [H0]
  · iexact H0
  · iexact HE

/-- Holding ownE ⊤ makes the finally-update at ⊤ trivial. -/
theorem own_fin [InvGS_gen .hasNoLC CGF] : (ownE ⊤ : IProp CGF) ⊢ iprop(|={⊤|}=> ⌜False⌝) := by
  unfold fupd_finally
  iintro H Hw HE
  ihave %hd : ⌜(⊤ : CoPset) ## ⊤⌝ $$ [H HE]
  · iapply ownE_disjoint
    isplitl [H] <;> iassumption
  exact absurd hd full_not_disj
end T1c5
open Iris Iris.BI T1c5

-- `Iris.fupd_finally_mask_mono` idx 6: necessary (E1 = ⊤, E2 = ∅: open the whole mask to get ownE ⊤, which makes |={⊤|}=> False trivial, then move it to mask ∅)
theorem t1c5_10 : ¬ drop0% Iris.fupd_finally_mask_mono 6 := fun h =>
  ffin_false (GF := CGF) fun {_} =>
    own_open.trans ((BIFUpdate.mono (own_fin.trans (h ⊤ ∅ _))).trans (fupd_fupd_finally ⊤ ∅ _))
namespace T1c5
open Iris Iris.BI COFE Auth

/-- Closed-proofs GF (invariant, mask, credit slots 0–3) with the functor F in every slot ≥ 4 (from W7c0). -/
noncomputable def GX (F : OFunctorPre) [RFunctorContractive F] [RFunctorAffine F] : BundledGFunctors := fun n =>
  match n with
  | 0  => ⟨InvMapF⟩
  | 1  => ⟨constOF CoPsetDisjL⟩
  | 2  => ⟨constOF (DisjointLeibnizSet PosSet)⟩
  | 3  => ⟨AuthURF (constOF Credit)⟩
  | _  => ⟨F⟩

section
variable (F : OFunctorPre) [RFunctorContractive F] [RFunctorAffine F]
instance gxWsat : WsatGpreS (GX F) where
  inv := { τ := 0, transp := by unfold GX; rfl }
  enabled := { τ := 1, transp := by unfold GX; rfl }
  disabled := { τ := 2, transp := by unfold GX; rfl }
instance gxLc : LcGpreS (GX F) where
  lc_elem := { τ := 3, transp := by unfold GX; rfl }
instance gxInv : InvGpreS (GX F) where
  toWsatGpreS := inferInstance
  toLcGpreS := inferInstance
instance gxElem : ElemG (GX F) F := { τ := 4, transp := by unfold GX; rfl }
end

instance boxGX : BoxG (GF := GX BoxF) := ⟨⟩

/-- Fancy-update soundness to ▷ False from ⊤ to any mask (from W7c0). -/
theorem fupd_later_false {GF : BundledGFunctors} [InvGpreS GF] (E2 : CoPset)
    (H : ∀ [InvGS_gen .hasNoLC GF], ⊢ (iprop(|={⊤,E2}=> ▷ ⌜False⌝) : IProp GF)) : False :=
  pure_soundness (PROP := IProp GF)
    (fupd_soundness .hasNoLC 0 (E1 := ⊤) (E2 := E2) (P := iprop(⌜False⌝)) fun _ =>
      wand_intro (sep_elim_left.trans (H.trans
        ((BIFUpdate.mono (or_intro_l (Q := iprop(⌜False⌝)))).trans fupd_except0))))

/-- ▷ (emp ≡ False ∗ P') gives ▷ False. -/
theorem eq_emp_false {GF : BundledGFunctors} (P' : IProp GF) :
    (iprop(▷ Iris.internalEq (PROP := IProp GF) (iprop(emp) : IProp GF) iprop(⌜False⌝ ∗ P')) : IProp GF) ⊢ ▷ ⌜False⌝ :=
  later_mono ((internalEq_iff (PROP := IProp GF) _ _).trans (and_elim_l.trans (by
    iintro H
    ihave H2 := H $$ []
    · itrivial
    icases H2 with ⟨%F, -⟩
    exact F.elim)))
theorem laterIf_false_elim {PROP : Type _} [BI PROP] {P : PROP} : iprop(▷?false P) ⊢ P := .rfl
end T1c5
open Iris Iris.BI T1c5

-- `Iris.slice_delete_empty` idx 13: necessary (GX with the box functor; an empty slice of ⌜False⌝ from box B1, used with a fresh empty box B2 that does not contain it: ▷ (emp ≡ False ∗ P'))
theorem t1c5_11 : ¬ drop0% Iris.slice_delete_empty 13 := fun h =>
  fupd_later_false (GF := GX BoxF) ⊤ fun {_} => by
    iintro
    ihave Hb := box_alloc (GF := GX BoxF) (M := TM) nroot
    ihave Hb2 := box_alloc (GF := GX BoxF) (M := TM) nroot
    imod slice_insert_empty (E := ⊤) (q := false) (f := (∅ : TM Bool)) (P := iprop(emp)) iprop(⌜False⌝) (N := nroot)
      $$ Hb with ⟨%γ, %Hγ, #Hs, Hb⟩
    imod h (E := ⊤) (q := false) (f := (∅ : TM Bool)) (P := iprop(emp)) (Q := iprop(⌜False⌝)) (γ := γ) (N := nroot)
      $$ [Hb2] with ⟨%P', H1, _⟩
    · isplitl []
      · iexact Hs
      · iexact Hb2
    imodintro
    iapply (laterIf_false_elim.trans (eq_emp_false P')) $$ H1
