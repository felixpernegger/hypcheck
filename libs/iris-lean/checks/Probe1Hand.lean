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
namespace Probe1
open Iris Iris.OFE

/-- Truncation OFE on naturals: dist n x y iff min x (n+1) = min y (n+1). Not discrete (1 and 2 agree at 0). -/
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
theorem tn_dist {n} {x y : TN} : x ≡{n}≡ y ↔ min x.v (n+1) = min y.v (n+1) := Iff.rfl
theorem tn12 : (⟨1⟩ : TN) ≡{0}≡ ⟨2⟩ := rfl
theorem tn12ne : (⟨1⟩ : TN) ≠ ⟨2⟩ := by simp
instance tn0disc : DiscreteE (⟨0⟩ : TN) := ⟨fun {y} h => by
  cases y with | mk v =>
    have h' : min 0 (0+1) = min v (0+1) := h
    have : v = 0 := by omega
    subst this; rfl⟩

-- `Iris.OFE.exist_ne` (hypothesis 7): necessary, TN, P a = (a = 1), a1=1, a2=2 agree at 0
theorem p1_39 : ¬ indep0% Iris.OFE.exist_ne 7 := fun h => tn12ne (@h TN _ (fun a => a = ⟨1⟩) 0 ⟨1⟩ ⟨2⟩ rfl tn12).symm
-- `Iris.Algebra.MonoidOps.op_dist` (hypothesis 9): necessary, TN, op a _ = if a=1 then 0 else 1: 1 and 2 agree at 0, images do not
theorem p1_31 : ¬ drop0% Iris.Algebra.MonoidOps.op_dist 9 := fun h => by
  have := @h TN _ ⟨0⟩ (fun a _ => if a.v = 1 then ⟨0⟩ else ⟨1⟩) 0 ⟨1⟩ ⟨2⟩ ⟨0⟩ ⟨0⟩ tn12 rfl
  simp [tn_dist] at this
-- `Iris.OFE.Option.merge_ne` (hypothesis 3): necessary, TN, op a _ = if a=1 then 0 else 1 is not non-expansive, neither is Option.merge op
theorem p1_37 : ¬ drop0% Iris.OFE.Option.merge_ne 3 := fun h => by
  have := (@h TN _ (fun a _ => if a.v = 1 then ⟨0⟩ else ⟨1⟩)).ne (n := 0) (x₁ := some ⟨1⟩) (x₂ := some ⟨2⟩) tn12 (y₁ := some ⟨0⟩) (y₂ := some ⟨0⟩) rfl
  simp [Option.merge, some_dist_some, tn_dist] at this
-- `Iris.ORA.Discrete.toDiscrete` (hypothesis 2): necessary, Excl TN is an ORA whose OFE is not discrete (excl 1 and excl 2 agree at 0)
theorem p1_10 : ¬ drop0% Iris.ORA.Discrete.toDiscrete 2 := fun h =>
  tn12ne (Excl.excl.inj ((@h (Excl TN) _).discrete_0 (x := Excl.excl ⟨1⟩) (y := .excl ⟨2⟩) tn12))
-- `Iris.Csum.instDiscrete_1` (hypothesis 4): necessary, alpha=Excl TN (not discrete), beta=Unit: Csum not discrete
theorem p1_16 : ¬ drop0% Iris.Csum.instDiscrete_1 4 := fun h => by
  have := (@h (Excl TN) Unit _ _ _).toDiscrete.discrete_0 (x := Csum.inl (.excl ⟨1⟩)) (y := Csum.inl (.excl ⟨2⟩)) tn12
  cases this
-- `Iris.cons_discrete` (hypothesis 5): necessary, TN, x=0 (discrete), l=[1]: [0,1] and [0,2] agree at 0 but differ
theorem p1_30 : ¬ drop0% Iris.cons_discrete 5 := fun h => by
  have := (@h TN _ ⟨0⟩ [⟨1⟩] _).discrete (y := [⟨0⟩, ⟨2⟩]) (.cons rfl (.cons tn12 .nil))
  simp at this
instance : Add TN := ⟨fun a b => ⟨a.v + b.v⟩⟩
-- `PosCommMonoidLike.instCancelable` (hypothesis 2): necessary, TN with +: associative, commutative, left cancellative, not discrete
theorem p1_34 : ¬ indep0% PosCommMonoidLike.instCancelable 2 := fun h => by
  have := (@h TN _ _ ⟨fun a b c => congrArg TN.mk (Nat.add_assoc a.v b.v c.v)⟩
    ⟨fun a b => congrArg TN.mk (Nat.add_comm a.v b.v)⟩
    ⟨fun {x₁ x₂ y} h => by
      cases x₁ with | mk a => cases x₂ with | mk b =>
      have h' : y.v + a = y.v + b := congrArg TN.v h
      simp only [TN.mk.injEq]; omega⟩ ⟨0⟩).discrete_0 tn12
  exact tn12ne this
-- `Iris.OFE.InvImage.equivalence` (hypothesis 4): necessary, r = False on True: InvImage r id not reflexive
theorem p1_36 : ¬ drop0% Iris.OFE.InvImage.equivalence 4 := fun h => (@h True True (fun _ _ => False) id).refl trivial
-- `Iris.OFE.ofe_mor_car_proper` (hypothesis 9): necessary, f=g=id on TN, x=1, y=2
theorem p1_38 : ¬ drop0% Iris.OFE.ofe_mor_car_proper 9 := fun h =>
  tn12ne (@h TN TN _ _ Hom.id Hom.id rfl ⟨1⟩ ⟨2⟩)
-- `Iris.fixpointK_proper` (hypothesis 8): removable, Hfg gives f = g by funext; the Contractive instances are Props, so rfl
theorem p1_43 : drop% Iris.fixpointK_proper 8 := by
  intro α _ _ k f g _ _ Hfg; have : f = g := funext Hfg; subst this; rfl
-- `Iris.Included.rfl` (hypothesis 2): necessary, Excl Unit: excl () is not included in itself (excl • z = invalid)
theorem p1_8 : ¬ drop0% Iris.Included.rfl 2 := fun h => by
  obtain ⟨z, hz⟩ := @h (Excl Unit) _ (.excl ()); cases z <;> cases hz
-- `Iris.IncludedN.rfl` (hypothesis 2): necessary, Excl Unit at n=0: excl () not n-included in itself
theorem p1_9 : ¬ drop0% Iris.IncludedN.rfl 2 := fun h => by
  obtain ⟨z, hz⟩ := @h (Excl Unit) _ 0 (.excl ()); cases z <;> cases hz
-- `Iris.Option.inc_of_some_inc_some` (hypothesis 2): necessary, Excl Unit: some y included in some x via none, y not included in x
theorem p1_13 : ¬ drop0% Iris.Option.inc_of_some_inc_some 2 := fun h => by
  obtain ⟨z, hz⟩ := @h (Excl Unit) _ (.excl ()) (.excl ()) ⟨none, rfl⟩; cases z <;> cases hz
-- `Iris.Update.option` (hypothesis 4): necessary, Excl Unit: excl () ~~> invalid fails at frame none
theorem p1_47 : ¬ drop0% Iris.Update.option 4 := fun h => by
  have := @h (Excl Unit) _ (.excl ()) .invalid 0 none trivial
  cases this
instance unitCanc : ∀ a : Unit, ORA.Cancelable a := fun _ => ⟨fun {n y z} _ _ => by cases y; cases z; exact OFE.Dist.of_eq rfl⟩
-- `Iris.Option.instCancelableOptionOfIdFree` (hypothesis 3): necessary, Unit: all elements cancelable, some () not cancelable in Option (none vs some ())
theorem p1_14 : ¬ drop0% Iris.Option.instCancelableOptionOfIdFree 3 := fun h => by
  have := (@h Unit _ (some ()) unitCanc).cancelableN (n := 0) (y := none) (z := some ()) trivial (OFE.Dist.of_eq rfl)
  exact not_none_dist_some this
-- `Iris.ORA.core_eq_self` (hypothesis 4): necessary, Option (Excl Unit) is total, core (some (excl ())) = none
theorem p1_12 : ¬ drop0% Iris.ORA.core_eq_self 4 := fun h => by
  have := @h (Option (Excl Unit)) _ (some (.excl ())) _
  cases this
instance unitMon : Algebra.MonoidOps (fun _ _ : Unit => ()) () where
  op_ne := ⟨fun _ _ _ _ _ _ _ => OFE.Dist.of_eq rfl⟩
  op_assoc := rfl
  op_comm := rfl
  op_left_id := rfl
-- `Iris.Algebra.BigOpL.bigOpL_hom_weak` (hypothesis 8): necessary, M1=TN with constant op 0 and unit 0 has no left identity (op 0 1 = 0)
theorem p1_5 : ¬ indep0% Iris.Algebra.BigOpL.bigOpL_hom_weak 8 := fun h => by
  have := (@h TN Unit _ _ (fun _ _ => ⟨0⟩) (fun _ _ => ()) ⟨0⟩ () unitMon Unit (fun _ _ => True) (fun _ => ()) [()] (fun _ _ => ⟨0⟩) (by simp)).op_left_id (a := ⟨1⟩)
  exact absurd (congrArg TN.v this) (by decide)
-- `View.bigOpL_frag` (hypothesis 5): necessary, R = False has no unit witness
theorem p1_49 : ¬ indep0% View.bigOpL_frag 5 := fun h => by
  obtain ⟨a, ha⟩ := (@h Unit Unit _ _ (fun _ _ _ => False) Unit (fun _ _ => ()) []).rel_unit 0
  exact ha
instance unitCore : ORA.CoreId () := ⟨rfl⟩
-- `Iris.isOp_pair_core_id_r` (hypothesis 10): necessary, alpha=MaxNat, beta=Unit, a=0, b1=b2=1: 0 is not max 1 1
theorem p1_25 : ¬ drop0% Iris.isOp_pair_core_id_r 10 := fun h => by
  have := congrArg (fun p => p.1.toNat) (@h MaxNat Unit _ _ .merge 0 1 1 () unitCore).is_op
  exact absurd this (by decide)
-- `Iris.MonoNat.instIsOpAuthMaxNatLb` (hypothesis 4): necessary, n=0, n1=n2=1: lb 0 is not lb 1 • lb 1
theorem p1_28 : ¬ drop0% Iris.MonoNat.instIsOpAuthMaxNatLb 4 := fun h => by
  have := congrArg (fun (v : MonoNat) => (View.frag v).toNat) (@h .merge 0 1 1).is_op
  exact absurd this (by decide)
-- `Auth.instIsOpViewAuthViewRelAuthOfDFrac` (hypothesis 7): necessary, A=Unit, dq=own 1, dq1=dq2=discard: auth fraction own 1 is not discard
theorem p1_2 : ¬ drop0% Auth.instIsOpViewAuthViewRelAuthOfDFrac 7 := fun h => by
  have := congrArg (fun v => v.auth.map (·.1)) (@h Unit _ .merge (.own 1) .discard .discard ()).is_op
  cases this
-- `Iris.Agree.Raw.op_sameElems` (hypothesis 5): necessary, a=[1], c=[2], b=d=[0] over Nat: 1 in a++b but not in c++d
theorem p1_0 : ¬ drop0% Iris.Agree.Raw.op_sameElems 5 := fun h => by
  have := (@h Nat ⟨[1], by simp⟩ ⟨[0], by simp⟩ ⟨[2], by simp⟩ ⟨[0], by simp⟩ ⟨fun _ h => h, fun _ h => h⟩).1 1
  simp [Agree.Raw.op] at this
-- `Iris.Agree.Raw.op_ne₂` (hypothesis 8): necessary, TN (truncation OFE), n=0, x1=x2=[0], y1=[5], y2=[0]: 5 has no 0-close partner
theorem p1_1 : ¬ drop0% Iris.Agree.Raw.op_ne₂ 8 := fun h => by
  have := (@h TN _ 0 ⟨[⟨0⟩], by simp⟩ ⟨[⟨0⟩], by simp⟩ ⟨[⟨5⟩], by simp⟩ ⟨[⟨0⟩], by simp⟩
    ⟨fun a ha => ⟨a, ha, OFE.Dist.of_eq rfl⟩, fun b hb => ⟨b, hb, OFE.Dist.of_eq rfl⟩⟩).1 ⟨5⟩
  simp [Agree.Raw.op, tn_dist] at this
-- `Iris.Algebra.BigOpL.bigOpL_zipWith_op_eq` (hypothesis 17): necessary, M=MaxNat with op, l1=[()], l2=[], Phi=1, Psi=0: unit=0 but rhs=1
theorem p1_4 : ¬ drop0% Iris.Algebra.BigOpL.bigOpL_zipWith_op_eq 17 := fun h => by
  have := @h MaxNat Unit _ ORA.op UORA.unit _ Unit (Unit × Unit) Prod.mk Prod.fst Prod.snd [()] []
    (fun _ _ => 1) (fun _ _ => 0) rfl rfl
  exact absurd (congrArg MaxNat.toNat this) (by decide)
-- `Iris.Algebra.BigOpM.bigOpM_op_eq` (hypothesis 4): necessary, M=TN with constant op 0 and unit 0 has no left identity (op 0 1 = 0)
theorem p1_6 : ¬ indep0% Iris.Algebra.BigOpM.bigOpM_op_eq 4 := fun h => by
  have := (@h TN _ (fun _ _ => ⟨0⟩) ⟨0⟩ (fun V => Std.ExtTreeMap Nat V compare) Nat Unit _ (fun _ _ => ⟨0⟩) (fun _ _ => ⟨0⟩) ∅).op_left_id (a := ⟨1⟩)
  exact absurd (congrArg TN.v this) (by decide)
instance ne3 : OFE.NonExpansive₃ (fun (_ _ z : TN) => z) := ⟨fun _ _ _ _ _ _ _ _ _ h => h⟩
-- `Iris.OFE.NonExpansive₃.ne` (hypothesis 19): necessary, f x y z = z on TN, z1=0, z2=1 at n=0
theorem p1_35 : ¬ drop0% Iris.OFE.NonExpansive₃.ne 19 := fun h => by
  have := @h TN TN TN TN _ _ _ _ _ ne3 0 ⟨0⟩ ⟨0⟩ rfl ⟨0⟩ ⟨0⟩ rfl ⟨0⟩ ⟨1⟩
  simp [tn_dist] at this
-- `Iris.Sum.map_ne` (hypothesis 12): necessary, A=Unit, f=const 0, f'=const 1 into TN, x=inl ()
theorem p1_41 : ¬ drop0% Iris.Sum.map_ne 12 := fun h => by
  have := @h Unit TN Unit Unit _ _ 0 (.inl ()) (fun _ => ⟨0⟩) (fun _ => ⟨1⟩) id id (fun _ => OFE.Dist.of_eq rfl)
  have h2 : (⟨0⟩ : TN) ≡{0}≡ ⟨1⟩ := this
  simp [tn_dist] at h2
/-- Discrete naturals with right-projection addition: associative, left identity 0, not commutative. -/
structure W1 where v : Nat
instance : OFE W1 := OFE.ofDiscrete W1
instance : OFE.Discrete W1 := ⟨fun h => h⟩
instance : Add W1 := ⟨fun _ y => y⟩
instance : Zero W1 := ⟨⟨0⟩⟩
instance : LE W1 := ⟨fun _ _ => True⟩
instance : Std.Associative (fun (x y : W1) => x + y) := ⟨fun _ _ _ => rfl⟩
instance : Std.LeftIdentity (fun (x y : W1) => x + y) (Zero.zero : W1) := ⟨⟩
instance : Std.LawfulLeftIdentity (fun (x y : W1) => x + y) Zero.zero := ⟨fun _ => rfl⟩
instance : LawfulAddLE W1 := ⟨fun {x y} => ⟨fun _ => ⟨y, rfl⟩, fun _ => trivial⟩⟩
-- `CommMonoidLike.ord_iff_le` (hypothesis 5): necessary, W1 with x+y=y: associative, left identity 0, LawfulAddLE with LE=True, not commutative
theorem p1_33 : ¬ indep0% CommMonoidLike.ord_iff_le 5 := fun h => by
  have := (@h W1 _ _ _ _ _ _ _ _ ⟨0⟩ ⟨0⟩).comm ⟨1⟩ ⟨2⟩
  exact absurd (congrArg W1.v this) (by decide)
/-- Commutative non-associative loop of order 6 with identity 0 (cancellative, not associative). -/
def lpTab : List Nat := [0,1,2,3,4,5, 1,0,3,2,5,4, 2,3,4,5,0,1, 3,2,5,4,1,0, 4,5,0,1,3,2, 5,4,1,0,2,3]
def lp (a b : Fin 6) : Fin 6 := ⟨lpTab.getD (a.val*6+b.val) 0 % 6, Nat.mod_lt _ (by decide)⟩
theorem lp_comm : ∀ a b : Fin 6, lp a b = lp b a := by decide
theorem lp_canc : ∀ a b c : Fin 6, lp c a = lp c b → a = b := by decide
theorem lp_id : ∀ a : Fin 6, lp 0 a = a := by decide
structure L6 where v : Fin 6
instance : OFE L6 := OFE.ofDiscrete L6
instance : OFE.Discrete L6 := ⟨fun h => h⟩
instance : Add L6 := ⟨fun a b => ⟨lp a.v b.v⟩⟩
instance : Zero L6 := ⟨⟨0⟩⟩
instance : Std.Commutative (fun (x y : L6) => x + y) := ⟨fun a b => congrArg L6.mk (lp_comm a.v b.v)⟩
instance : Std.LeftIdentity (fun (x y : L6) => x + y) (Zero.zero : L6) := ⟨⟩
instance : Std.LawfulLeftIdentity (fun (x y : L6) => x + y) Zero.zero := ⟨fun a => congrArg L6.mk (lp_id a.v)⟩
instance : LeftCancelAdd L6 := ⟨fun {x₁ x₂ y} e => by
  cases x₁; cases x₂; exact congrArg L6.mk (lp_canc _ _ _ (congrArg L6.v e))⟩
-- `CommMonoidLike.instCancelable` (hypothesis 4): necessary, L6 (commutative non-associative loop of order 6): cancellative, left identity 0, not associative
theorem p1_32 : ¬ indep0% CommMonoidLike.instCancelable 4 := fun h => by
  have := (@h L6 _ _ _ _ _ _ _ ⟨0⟩).assoc ⟨2⟩ ⟨2⟩ ⟨4⟩
  exact absurd (congrArg L6.v this) (by decide)
instance infNat : InfiniteType Nat := ⟨id, fun _ _ h => h⟩
-- `DisjointLeibnizSet.alloc_updateP` (hypothesis 7): necessary, ExtTreeSet Nat, Q = False, X = empty: no update target
theorem p1_27 : ¬ drop0% DisjointLeibnizSet.alloc_updateP 7 := fun h => by
  obtain ⟨y, hy, -⟩ := @h Nat (Std.ExtTreeSet Nat compare) _ _ infNat (fun _ => False) ∅ 0 none trivial
  exact hy
-- `DisjointLeibnizSet.localUpdate_op_r` (hypothesis 7): necessary, ExtTreeSet Nat, X=Y=Z={0}: valid Z • valid X is error
theorem p1_26 : ¬ drop0% DisjointLeibnizSet.localUpdate_op_r 7 := fun h => by
  have := (@h Nat (Std.ExtTreeSet Nat compare) _ _ {0} {0} {0} 0 none trivial rfl).1
  have h2 := DisjointLeibnizSet.valid_op_iff_disj.mp (ORA.discrete_valid this)
  exact h2 0 ⟨Std.LawfulSet.mem_singleton.mpr rfl, Std.LawfulSet.mem_singleton.mpr rfl⟩
-- `Iris.ReservationMap.valid_token_of_valid` (hypothesis 5): necessary, token = error: invalid
theorem p1_44 : ¬ drop0% Iris.ReservationMap.valid_token_of_valid 5 := fun h =>
  DisjointLeibnizSet.not_valid_invalid (S := CoPset) (@h (fun A => Pos → Option A) Unit _ _ ⟨fun _ => none, .error⟩)
-- `Iris.UPred.mono_unpacked` (hypothesis 9): necessary, UPred over Unit that is always False
theorem p1_46 : ¬ drop0% Iris.UPred.mono_unpacked 9 := fun h =>
  @h Unit _ ⟨fun _ _ => False, fun h _ _ => h⟩ 0 0 () () trivial trivial (by first | exact ⟨(), OFE.Dist.of_eq rfl⟩ | exact ⟨(), rfl⟩ | trivial) (Nat.le_refl 0)
/-- View relation on truncation naturals: holds at step 0, or when the authoritative part is 0. -/
def tnRel : ViewRel TN Unit := fun n a _ => n = 0 ∨ a.v = 0
instance tnRelIs : IsViewRel tnRel where
  mono {n1 a1 b1 n2 a2 b2} H Ha _ Hn := by
    have Ha' : min a1.v (n2+1) = min a2.v (n2+1) := Ha
    unfold tnRel at *; omega
  op_left H := H
  rel_validN _ _ _ _ := trivial
  rel_unit _ := ⟨⟨0⟩, .inr rfl⟩
-- `IsViewRel.mono_inc` (hypothesis 15): necessary, TN, relation n=0 or a=0; n1=0, n2=1, a=1
theorem p1_48 : ¬ drop0% IsViewRel.mono_inc 15 := fun h => by
  have := @h TN Unit 0 ⟨1⟩ () 1 ⟨1⟩ () _ _ tnRel tnRelIs (.inl rfl) rfl ⟨(), OFE.Dist.of_eq rfl⟩
  simp [tnRel] at this
-- `Auth.auth_local_update_ord` (hypothesis 9): necessary, A=MaxNat, a=a'=0, (0,0)~l~>(1,1): result auth 0 with frag 1 is invalid
theorem p1_3 : ¬ drop0% Auth.auth_local_update_ord 9 := fun h => by
  have hup : ((0 : MaxNat), (0 : MaxNat)) ~l~> (1, 1) := MaxNat.local_update (show (0:MaxNat).toNat ≤ (1:MaxNat).toNat by decide)
  have := (@h MaxNat _ 0 0 0 0 1 1 hup trivial 0 none
    (Auth.both_validN_ord.mpr ⟨ORA.ordN_of_ord 0 (MaxNat.ord_iff.mpr (show (0:MaxNat).toNat ≤ (0:MaxNat).toNat by decide)), trivial⟩)
    (OFE.Dist.of_eq rfl)).1
  have h2 := MaxNat.ord_iff.mp (ORA.discrete_ord (Auth.both_validN_ord.mp this).1)
  exact absurd h2 (show ¬ (1:MaxNat).toNat ≤ (0:MaxNat).toNat by decide)
abbrev FH := fun A => Pos → Option A
-- `Iris.DynReservationMap.validN_mono` (hypothesis 9): necessary, token error for x, y = unit: x invalid, y valid (DynReservationMap over Pos -> Option)
theorem p1_18 : ¬ drop0% Iris.DynReservationMap.validN_mono 9 := fun h =>
  @h Unit FH _ _ 0 ⟨(UORA.unit : DynReservationMap Unit FH).data, .error⟩ UORA.unit id (fun _ h => h) (show ✓{0} (UORA.unit : DynReservationMap Unit FH) from ORA.unit_validN)
-- `Iris.ReservationMap.validN_mono` (hypothesis 8): necessary, x.data all some (), tokens {1} for x and y, y.data empty: x invalid
theorem p1_45 : ¬ drop0% Iris.ReservationMap.validN_mono 8 := fun h => by
  have := @h FH Unit _ _ 0 ⟨fun _ => some (), .valid {1}⟩ ⟨fun _ => none, .valid {1}⟩ (fun _ _ => trivial)
    ⟨UORA.unit, ORA.unit_right_id.symm⟩ ⟨fun _ => trivial, fun _ => .inl rfl⟩
  rcases this.2 1 with h1 | h1
  · cases h1
  · exact h1 (Std.LawfulSet.mem_singleton.mpr rfl)
abbrev TM := fun V => Std.ExtTreeMap Nat V compare
-- `Heap.alloc_updateP_strong_dep` (hypothesis 10): necessary, Excl Unit, f = invalid, Q = not valid at 0: no valid allocation
theorem p1_21 : ¬ drop0% Heap.alloc_updateP_strong_dep 10 := fun h => by
  obtain ⟨y, hy, hv⟩ := @h TM Nat (Excl Unit) _ _ (fun m' => ¬ ✓{0} m') (· ∉ ([] : List Nat)) ∅ (fun _ => .invalid)
    (PredInfinite.not_mem []) (fun i _ _ hv => by have := hv i; simp [Iris.Std.LawfulPartialMap.get?_insert] at this; cases this) 0 none
    (ORA.valid_iff_validN.mp Heap.valid_empty 0)
  exact hy hv
-- `Heap.alloc_updateP_cofinite` (hypothesis 10): necessary, Excl Unit, x = invalid, Q = not valid at 0: no valid allocation
theorem p1_22 : ¬ drop0% Heap.alloc_updateP_cofinite 10 := fun h => by
  obtain ⟨y, hy, hv⟩ := @h TM Nat (Excl Unit) _ _ infNat (fun m' => ¬ ✓{0} m') ∅ .invalid []
    (fun i _ _ hv => by have := hv i; simp [Iris.Std.LawfulPartialMap.get?_insert] at this; cases this) 0 none
    (ORA.valid_iff_validN.mp Heap.valid_empty 0)
  exact hy hv
instance unitIsOp : IsOp .merge () () () := ⟨rfl⟩
-- `HeapView.instIsOpViewSemiOutParamCoreToInOutProdDFracHeapRFrag` (hypothesis 13): necessary, V=Unit, dp=own 1, dp1=dp2=discard over Nat -> Option heaps
theorem p1_23 : ¬ drop0% HeapView.instIsOpViewSemiOutParamCoreToInOutProdDFracHeapRFrag 13 := fun h => by
  have := congrArg (fun v => ((View.frag v) 0).map (·.1)) (@h Nat Unit (fun V => Nat → Option V) _ _ (.own 1) 0 () () .merge .discard .discard () unitIsOp).is_op
  first | cases this | (injection this with e; cases e) | (simp [HeapView.Frag, Heap.get?_op] at this)
/-- Discrete ORA on booleans: op is and, no core, order is equality. Not IncOrd, false not Increasing. -/
structure BA where b : Bool
instance : OFE BA := OFE.ofDiscrete BA
instance : OFE.Discrete BA := ⟨fun h => h⟩
def baData : DiscreteORAData BA where
  pcore _ := none
  op x y := ⟨x.b && y.b⟩
  Valid _ := True
  Order := Eq
  assoc x y z := congrArg BA.mk (Bool.and_assoc x.b y.b z.b).symm
  comm x y := congrArg BA.mk (Bool.and_comm x.b y.b)
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
instance baORA : ORA BA := ORA.ofDiscreteORAData baData
theorem ba_not_inc : ¬ Increasing (⟨false⟩ : BA) := fun h => by
  have := h.increasing ⟨true⟩
  cases this
-- `Iris.Increasing.of_ordNR` (hypothesis 5): necessary, BA (Bool, and, order Eq): x=y=false, false is not Increasing
theorem p1_11 : ¬ drop0% Iris.Increasing.of_ordNR 5 := fun h =>
  ba_not_inc (@h BA _ 0 ⟨false⟩ ⟨false⟩ (.inl (OFE.Dist.of_eq rfl)))
-- `Iris.Prod.instIsInc` (hypothesis 4): necessary, alpha=BA (not IncOrd), beta=Unit: (true,()) included in (false,()) but not ordered
theorem p1_15 : ¬ drop0% Iris.Prod.instIsInc 4 := fun h => by
  have := (@h BA Unit _ _ inferInstance).inc_ord (x := (⟨true⟩, ())) (y := (⟨false⟩, ())) ⟨(⟨false⟩, ()), rfl⟩
  cases this.1
-- `Heap.singleton_ordN_iff` (hypothesis 8): necessary, V=BA, m = 0:true, else false; singleton 0 true not below m (none vs non-increasing false)
theorem p1_19 : ¬ drop0% Heap.singleton_ordN_iff 8 := fun h => by
  have := (@h (fun V => Nat → Option V) Nat BA _ _ 0 0 ⟨true⟩ (fun k => if k = 0 then some ⟨true⟩ else some ⟨false⟩)).mpr
    ⟨⟨true⟩, OFE.Dist.of_eq rfl, .inl (OFE.Dist.of_eq rfl)⟩ 1
  exact ba_not_inc this
section
attribute [local instance] lexOrd
-- `Iris.SetBijective.eq_iff` (hypothesis 11): necessary, L={(0,0)}, a1=a2=0, b1=0, b2=1 (ExtTreeSet over Nat x Nat, lexOrd)
theorem p1_29 : ¬ drop0% Iris.SetBijective.eq_iff 11 := fun h => by
  have := @h (Std.ExtTreeSet (Nat × Nat) compare) Nat Nat _ 0 0 0 1 {(0, 0)}
    (fun hab => by
      rw [Std.LawfulSet.mem_singleton] at hab
      cases hab
      exact ⟨fun b' hb' => by rw [Std.LawfulSet.mem_singleton] at hb'; cases hb'; rfl,
             fun a' ha' => by rw [Std.LawfulSet.mem_singleton] at ha'; cases ha'; rfl⟩)
    (Std.LawfulSet.mem_singleton.mpr rfl)
  exact absurd (this.mp rfl) (by decide)
end
-- `Iris.Algebra.BigOpM.bigOpM_sep_zip_eq` (hypothesis 14): necessary, MaxNat, m1={0:()}, m2=empty, h1=1, h2=0: zip is empty, lhs=0, rhs=1
theorem p1_7 : ¬ drop0% Iris.Algebra.BigOpM.bigOpM_sep_zip_eq 14 := fun h => by
  have := @h MaxNat _ ORA.op UORA.unit _ (fun V => Std.ExtTreeMap Nat V compare) Nat _ Unit Unit (fun _ _ => 1) (fun _ _ => 0)
    (Iris.Std.PartialMap.singleton (M := fun V => Std.ExtTreeMap Nat V compare) 0 ()) (∅ : Std.ExtTreeMap Nat Unit compare)
  rw [Iris.Std.LawfulPartialMap.zip_empty_right, Algebra.BigOpM.bigOpM_empty, Algebra.BigOpM.bigOpM_singleton_eq,
    Algebra.BigOpM.bigOpM_empty] at this
  exact absurd (congrArg MaxNat.toNat this) (by decide)
/-- Discrete ORA on Nat × Bool: (a, p) • (b, q) = (a + b + 1, p && q), no core, order is equality.
Every element is IdFree, but (0, false) is not cancelable. -/
structure NB where
  n : Nat
  b : Bool
instance : OFE NB := OFE.ofDiscrete NB
instance : OFE.Discrete NB := ⟨fun h => h⟩
def nbData : DiscreteORAData NB where
  pcore _ := none
  op x y := ⟨x.n + y.n + 1, x.b && y.b⟩
  Valid _ := True
  Order := Eq
  assoc x y z := by cases x; cases y; cases z; simp [Bool.and_assoc]; try omega
  comm x y := by cases x; cases y; simp [Bool.and_comm]; try omega
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
instance nbORA : ORA NB := ORA.ofDiscreteORAData nbData
instance nbIdFree : ∀ x : NB, ORA.IdFree x := fun x => ⟨fun y _ h => by
  have : x.n + y.n + 1 = x.n := congrArg NB.n h
  omega⟩
abbrev FN := fun V => Nat → Option V
-- `Heap.instCancelableOfIdFree` (hypothesis 7): necessary, V=NB ((a,p)•(b,q)=(a+b+1,p&&q)): all IdFree, heap {0:(0,false)} not cancelable
theorem p1_20 : ¬ drop0% Heap.instCancelableOfIdFree 7 := fun h => by
  have := (@h FN Nat NB _ _ (fun k => if k = 0 then some ⟨0, false⟩ else none) nbIdFree).cancelableN (n := 0)
    (y := fun k => if k = 0 then some ⟨0, true⟩ else none) (z := fun k => if k = 0 then some ⟨0, false⟩ else none)
    (fun k => by rcases k with _|k <;> exact trivial)
    (OFE.Dist.of_eq (funext fun k => by rcases k with _|k <;> rfl))
  have h0 := this 0
  cases h0
-- `Iris.LimitPreserving.compl` (hypothesis 3): necessary, SiProp, chain c n = holds below n, P x = some step fails; limit holds everywhere
theorem p1_42 : ¬ drop0% Iris.LimitPreserving.compl 3 := fun h => by
  have := @h SiProp inferInstance (fun x => ∃ k, ¬ x.holds k)
    ⟨fun n => ⟨fun i => i ≤ n, fun h1 h2 => Nat.le_trans h2 h1⟩, fun {n i} hni {m} hm => by
      show m ≤ i ↔ m ≤ n; omega⟩
    (fun n => ⟨n+1, fun h => by change n+1 ≤ n at h; omega⟩)
  obtain ⟨k, hk⟩ := this
  exact hk (Nat.le_refl k)
-- `Iris.Csum.instRFunctorAffine` (hypothesis 5): necessary, Fa=constOF Unit, Fb=constOF BA: inr true included in inr false but not ordered
theorem p1_17 : ¬ drop0% Iris.Csum.instRFunctorAffine 5 := fun h => by
  have := (@h (constOF Unit) (constOF BA) _ _ inferInstance).affine (α := Unit) (β := Unit)
  have h2 := this.inc_ord (x := (Csum.inr ⟨true⟩ : Csum Unit BA)) (y := .inr ⟨false⟩) ⟨.inr ⟨false⟩, rfl⟩
  cases h2
def sTrue : SiProp := ⟨fun _ => True, fun h _ => h⟩
def sFalse : SiProp := ⟨fun _ => False, fun h _ => h⟩
-- `Iris.COFE.OFunctorContractive.map_distLater` (hypothesis 16): necessary, F = LaterOF IdOF, n=1, g1 = const True, g2 = const False into SiProp
theorem p1_40 : ¬ drop0% Iris.COFE.OFunctorContractive.map_distLater 16 := fun h => by
  have := @h Unit Unit Unit SiProp (LaterOF IdOF) _ _ _ _ _ 1 Hom.id Hom.id
    ⟨Function.const _ sTrue, const_ne⟩ ⟨Function.const _ sFalse, const_ne⟩ (fun _ _ => OFE.Dist.of_eq rfl) ⟨()⟩
  have h2 : sTrue ≡{0}≡ sFalse := this 0 (by omega)
  exact (h2 (m := 0) (Nat.le_refl 0)).mp trivial
-- `HeapView.auth_op_frag_validN_iff_ord` (hypothesis 11): necessary, V=BA, m1 = all false, dq=discard, v=true: frame (discard,false) exists, order fails
theorem p1_24 : ¬ drop0% HeapView.auth_op_frag_validN_iff_ord 11 := fun h => by
  have lhs := (HeapView.auth_op_frag_validN_iff_frame (H := fun V => Nat → Option V) (K := Nat) (V := BA) (n := 0)
    (dp := .discard) (m1 := fun _ => some ⟨false⟩) (k := 0) (dq := .discard) (v := ⟨true⟩)).mpr
    ⟨⟨false⟩, .discard, trivial, rfl, ⟨trivial, trivial⟩, some (.discard, ⟨false⟩), .inl (OFE.Dist.of_eq rfl)⟩
  obtain ⟨v', dq', -, hget, -, hord⟩ := h.mp lhs
  cases hget
  rcases hord with hd | ho
  · have := congrArg (fun p => p.2.b) (OFE.Discrete.discrete_0 hd)
    cases this
  · cases ho.2
end Probe1
