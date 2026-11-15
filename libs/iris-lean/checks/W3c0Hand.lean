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

namespace W3c0
open Iris Iris.OFE

/-- Truncation OFE on any type with an injective map to Nat: n-distance compares min v (n+1); not discrete. -/
def tnOFEOf {α : Type} (f : α → Nat) (inj : ∀ a b, f a = f b → a = b) : OFE α where
  Dist n x y := min (f x) (n+1) = min (f y) (n+1)
  dist_eqv := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩
  eq_dist' {x y} := ⟨fun h n => h ▸ rfl, fun h => by
      have h' : min (f x) (f x + f y + 1) = min (f y) (f x + f y + 1) := h (f x + f y)
      exact inj _ _ (by omega)⟩
  dist_lt {n x y m} h hm := by
    have h' : min (f x) (n+1) = min (f y) (n+1) := h
    show min (f x) (m+1) = min (f y) (m+1); omega

/-- Two 0-close but distinct elements refute discreteness. -/
theorem nd_of {α : Type} [OFE α] (x y : α) (h0 : x ≡{0}≡ y) (hne : x ≠ y) : ¬ OFE.Discrete α :=
  fun h => hne (h.discrete_0 h0)
theorem nde_of {α : Type} [OFE α] (x y : α) (h0 : x ≡{0}≡ y) (hne : x ≠ y) : ¬ OFE.DiscreteE x :=
  fun h => hne (h.discrete h0)

/-- TA: truncation OFE on Nat with +, zero 0 (lawful), left cancellative, LE := exists-add; not discrete. -/
structure TA where v : Nat
instance : OFE TA := tnOFEOf TA.v (fun a b h => by cases a; cases b; cases h; rfl)
instance : Inhabited TA := ⟨⟨0⟩⟩
instance : Add TA := ⟨fun a b => ⟨a.v + b.v⟩⟩
instance : Zero TA := ⟨⟨0⟩⟩
instance : LE TA := ⟨fun x y => ∃ z, y = x + z⟩
instance : LawfulAddLE TA := ⟨Iff.rfl⟩
instance : Std.Associative (fun (x y : TA) => x + y) := ⟨fun a b c => congrArg TA.mk (Nat.add_assoc a.v b.v c.v)⟩
instance : Std.Commutative (fun (x y : TA) => x + y) := ⟨fun a b => congrArg TA.mk (Nat.add_comm a.v b.v)⟩
instance : Std.LeftIdentity (fun (x y : TA) => x + y) (Zero.zero : TA) := ⟨⟩
instance : Std.LawfulLeftIdentity (fun (x y : TA) => x + y) Zero.zero := ⟨fun a => congrArg TA.mk (Nat.zero_add a.v)⟩
instance : LeftCancelAdd TA := ⟨fun {x₁ x₂ y} e => by
  cases x₁ with | mk a => cases x₂ with | mk b =>
  have h : y.v + a = y.v + b := congrArg TA.v e
  exact congrArg TA.mk (by omega)⟩
theorem ta_nd : ¬ OFE.Discrete TA := nd_of (⟨1⟩ : TA) ⟨2⟩ rfl (by simp)
theorem ta_nde : ¬ OFE.DiscreteE (⟨1⟩ : TA) := nde_of (⟨1⟩ : TA) ⟨2⟩ rfl (by simp)

/-- TX: truncation OFE on Nat with max (associative, commutative, idempotent); not discrete. -/
structure TX where v : Nat
instance : OFE TX := tnOFEOf TX.v (fun a b h => by cases a; cases b; cases h; rfl)
instance : Inhabited TX := ⟨⟨0⟩⟩
instance : Add TX := ⟨fun a b => ⟨max a.v b.v⟩⟩
instance : Std.Associative (fun (x y : TX) => x + y) := ⟨fun a b c => congrArg TX.mk (Nat.max_assoc a.v b.v c.v)⟩
instance : Std.Commutative (fun (x y : TX) => x + y) := ⟨fun a b => congrArg TX.mk (Nat.max_comm a.v b.v)⟩
instance : Std.IdempotentOp (fun (x y : TX) => x + y) := ⟨fun a => congrArg TX.mk (Nat.max_self a.v)⟩
theorem tx_nd : ¬ OFE.Discrete TX := nd_of (⟨1⟩ : TX) ⟨2⟩ rfl (by simp)

/-- TP: truncation OFE on Nat with a+b+1 (associative, commutative, identity free, left cancellative), LT := exists-add. -/
structure TP where v : Nat
instance : OFE TP := tnOFEOf TP.v (fun a b h => by cases a; cases b; cases h; rfl)
instance : Inhabited TP := ⟨⟨0⟩⟩
instance : Add TP := ⟨fun a b => ⟨a.v + b.v + 1⟩⟩
instance : LT TP := ⟨fun x y => ∃ z, y = x + z⟩
instance : LawfulAddLT TP := ⟨Iff.rfl⟩
instance : Std.Associative (fun (x y : TP) => x + y) := ⟨fun a b c => congrArg TP.mk (by show a.v + b.v + 1 + c.v + 1 = a.v + (b.v + c.v + 1) + 1; omega)⟩
instance : Std.Commutative (fun (x y : TP) => x + y) := ⟨fun a b => congrArg TP.mk (by show a.v + b.v + 1 = b.v + a.v + 1; omega)⟩
instance : IdentityFree TP := ⟨fun {a b} e => by have := congrArg TP.v e; simp only [Add.add] at this; omega⟩
instance : LeftCancelAdd TP := ⟨fun {x₁ x₂ y} e => by
  cases x₁ with | mk a => cases x₂ with | mk b =>
  have h : y.v + a + 1 = y.v + b + 1 := congrArg TP.v e
  exact congrArg TP.mk (by omega)⟩
theorem tp_nd : ¬ OFE.Discrete TP := nd_of (⟨1⟩ : TP) ⟨2⟩ rfl (by simp)

/-- Commutative non-associative loop of order 6 with identity 0 (cancellative), copied from Probe1. -/
def lpTab : List Nat := [0,1,2,3,4,5, 1,0,3,2,5,4, 2,3,4,5,0,1, 3,2,5,4,1,0, 4,5,0,1,3,2, 5,4,1,0,2,3]
def lp (a b : Fin 6) : Fin 6 := ⟨lpTab.getD (a.val*6+b.val) 0 % 6, Nat.mod_lt _ (by decide)⟩
theorem lp_comm : ∀ a b : Fin 6, lp a b = lp b a := by decide
theorem lp_canc : ∀ a b c : Fin 6, lp c a = lp c b → a = b := by decide
theorem lp_id : ∀ a : Fin 6, lp 0 a = a := by decide
structure L6 where v : Fin 6
instance : OFE L6 := OFE.ofDiscrete L6
instance : OFE.Discrete L6 := ⟨fun h => h⟩
instance : Inhabited L6 := ⟨⟨0⟩⟩
instance : Add L6 := ⟨fun a b => ⟨lp a.v b.v⟩⟩
instance : Zero L6 := ⟨⟨0⟩⟩
instance : LE L6 := ⟨fun x y => ∃ z, y = x + z⟩
instance : LawfulAddLE L6 := ⟨Iff.rfl⟩
instance : Std.Commutative (fun (x y : L6) => x + y) := ⟨fun a b => congrArg L6.mk (lp_comm a.v b.v)⟩
instance : Std.LeftIdentity (fun (x y : L6) => x + y) (Zero.zero : L6) := ⟨⟩
instance : Std.LawfulLeftIdentity (fun (x y : L6) => x + y) Zero.zero := ⟨fun a => congrArg L6.mk (lp_id a.v)⟩
instance : LeftCancelAdd L6 := ⟨fun {x₁ x₂ y} e => by
  cases x₁; cases x₂; exact congrArg L6.mk (lp_canc _ _ _ (congrArg L6.v e))⟩
theorem l6_na : ¬ Std.Associative (fun (x y : L6) => x + y) := fun h =>
  absurd (congrArg L6.v (h.assoc ⟨2⟩ ⟨2⟩ ⟨4⟩)) (by decide)

/-- Steiner quasigroup on Fin 3: a+b = 2a+2b mod 3; commutative, idempotent, left cancellative, not associative. -/
def st (a b : Fin 3) : Fin 3 := ⟨(2*a.val+2*b.val) % 3, Nat.mod_lt _ (by decide)⟩
theorem st_comm : ∀ a b : Fin 3, st a b = st b a := by decide
theorem st_idem : ∀ a : Fin 3, st a a = a := by decide
theorem st_canc : ∀ a b c : Fin 3, st c a = st c b → a = b := by decide
structure S3 where v : Fin 3
instance : OFE S3 := OFE.ofDiscrete S3
instance : OFE.Discrete S3 := ⟨fun h => h⟩
instance : Inhabited S3 := ⟨⟨0⟩⟩
instance : Add S3 := ⟨fun a b => ⟨st a.v b.v⟩⟩
instance : Std.Commutative (fun (x y : S3) => x + y) := ⟨fun a b => congrArg S3.mk (st_comm a.v b.v)⟩
instance : Std.IdempotentOp (fun (x y : S3) => x + y) := ⟨fun a => congrArg S3.mk (st_idem a.v)⟩
instance : LeftCancelAdd S3 := ⟨fun {x₁ x₂ y} e => by
  cases x₁; cases x₂; exact congrArg S3.mk (st_canc _ _ _ (congrArg S3.v e))⟩
theorem s3_na : ¬ Std.Associative (fun (x y : S3) => x + y) := fun h =>
  absurd (congrArg S3.v (h.assoc ⟨0⟩ ⟨0⟩ ⟨1⟩)) (by decide)

/-- NQ: discrete Nat with a+b := a*b+a+b+1: commutative, left cancellative, identity free, not associative. -/
structure NQ where v : Nat
instance : OFE NQ := OFE.ofDiscrete NQ
instance : OFE.Discrete NQ := ⟨fun h => h⟩
instance : Inhabited NQ := ⟨⟨0⟩⟩
instance : Add NQ := ⟨fun a b => ⟨a.v * b.v + a.v + b.v + 1⟩⟩
instance : LT NQ := ⟨fun x y => ∃ z, y = x + z⟩
instance : LawfulAddLT NQ := ⟨Iff.rfl⟩
instance : Std.Commutative (fun (x y : NQ) => x + y) := ⟨fun a b => congrArg NQ.mk (by
  show a.v * b.v + a.v + b.v + 1 = b.v * a.v + b.v + a.v + 1; rw [Nat.mul_comm]; omega)⟩
instance : IdentityFree NQ := ⟨fun {a b} e => by have := congrArg NQ.v e; simp only [Add.add] at this; omega⟩
instance : LeftCancelAdd NQ := ⟨fun {x₁ x₂ y} e => by
  cases x₁ with | mk a => cases x₂ with | mk b =>
  have h : y.v * a + y.v + a + 1 = y.v * b + y.v + b + 1 := congrArg NQ.v e
  have h2 : (y.v + 1) * a = (y.v + 1) * b := by rw [Nat.add_mul, Nat.add_mul, Nat.one_mul, Nat.one_mul]; omega
  exact congrArg NQ.mk (Nat.eq_of_mul_eq_mul_left (Nat.succ_pos _) h2)⟩
theorem nq_na : ¬ Std.Associative (fun (x y : NQ) => x + y) := fun h =>
  absurd (congrArg NQ.v (h.assoc ⟨1⟩ ⟨1⟩ ⟨0⟩)) (by decide)

/-- W1: discrete Nat with x+y := y: associative, idempotent, left cancellative, every element a left identity; not commutative. -/
structure W1 where v : Nat
instance : OFE W1 := OFE.ofDiscrete W1
instance : OFE.Discrete W1 := ⟨fun h => h⟩
instance : Inhabited W1 := ⟨⟨0⟩⟩
instance : Add W1 := ⟨fun _ y => y⟩
instance : Zero W1 := ⟨⟨0⟩⟩
instance : LE W1 := ⟨fun x y => ∃ z, y = x + z⟩
instance : LawfulAddLE W1 := ⟨Iff.rfl⟩
instance : Std.Associative (fun (x y : W1) => x + y) := ⟨fun _ _ _ => rfl⟩
instance : Std.IdempotentOp (fun (x y : W1) => x + y) := ⟨fun _ => rfl⟩
instance : Std.LeftIdentity (fun (x y : W1) => x + y) (Zero.zero : W1) := ⟨⟩
instance : Std.LawfulLeftIdentity (fun (x y : W1) => x + y) Zero.zero := ⟨fun _ => rfl⟩
instance : LeftCancelAdd W1 := ⟨fun e => e⟩
theorem w1_nc : ¬ Std.Commutative (fun (x y : W1) => x + y) := fun h =>
  absurd (congrArg W1.v (h.comm ⟨1⟩ ⟨2⟩)) (by decide)

/-- LW: discrete free semigroup, lists of Bool with a+b := a ++ true :: b: associative, left cancellative, identity free, LT := exists-add; not commutative. -/
structure LW where v : List Bool
instance : OFE LW := OFE.ofDiscrete LW
instance : OFE.Discrete LW := ⟨fun h => h⟩
instance : Inhabited LW := ⟨⟨[]⟩⟩
instance : Add LW := ⟨fun a b => ⟨a.v ++ true :: b.v⟩⟩
instance : LT LW := ⟨fun x y => ∃ z, y = x + z⟩
instance : LawfulAddLT LW := ⟨Iff.rfl⟩
instance : Std.Associative (fun (x y : LW) => x + y) := ⟨fun a b c => congrArg LW.mk (by
  show (a.v ++ true :: b.v) ++ true :: c.v = a.v ++ true :: (b.v ++ true :: c.v); simp)⟩
instance : IdentityFree LW := ⟨fun {a b} e => by
  have := congrArg (fun x : LW => x.v.length) e; simp [Add.add] at this⟩
instance : LeftCancelAdd LW := ⟨fun {x₁ x₂ y} e => by
  cases x₁ with | mk a => cases x₂ with | mk b =>
  have h : y.v ++ true :: a = y.v ++ true :: b := congrArg LW.v e
  simp at h; exact congrArg LW.mk h⟩
theorem lw_nc : ¬ Std.Commutative (fun (x y : LW) => x + y) := fun h =>
  absurd (congrArg LW.v (h.comm ⟨[]⟩ ⟨[false]⟩)) (by decide)

/-- ZN: discrete Nat with +, but Zero := 1 (not a left identity); associative, commutative, left cancellative, not idempotent. -/
structure ZN where v : Nat
instance : OFE ZN := OFE.ofDiscrete ZN
instance : OFE.Discrete ZN := ⟨fun h => h⟩
instance : Inhabited ZN := ⟨⟨0⟩⟩
instance : Add ZN := ⟨fun a b => ⟨a.v + b.v⟩⟩
instance : Zero ZN := ⟨⟨1⟩⟩
instance : LE ZN := ⟨fun x y => ∃ z, y = x + z⟩
instance : LawfulAddLE ZN := ⟨Iff.rfl⟩
instance : Std.Associative (fun (x y : ZN) => x + y) := ⟨fun a b c => congrArg ZN.mk (Nat.add_assoc a.v b.v c.v)⟩
instance : Std.Commutative (fun (x y : ZN) => x + y) := ⟨fun a b => congrArg ZN.mk (Nat.add_comm a.v b.v)⟩
instance : LeftCancelAdd ZN := ⟨fun {x₁ x₂ y} e => by
  cases x₁ with | mk a => cases x₂ with | mk b =>
  have h : y.v + a = y.v + b := congrArg ZN.v e
  exact congrArg ZN.mk (by omega)⟩
theorem zn_nl : ¬ Std.LawfulLeftIdentity (fun (x y : ZN) => x + y) (Zero.zero : ZN) := fun h =>
  absurd (congrArg ZN.v (h.left_id ⟨0⟩)) (by decide)
theorem zn_ni : ¬ Std.IdempotentOp (fun (x y : ZN) => x + y) := fun h =>
  absurd (congrArg ZN.v (h.idempotent ⟨1⟩)) (by decide)

/-- BO: discrete Bool with or (associative, commutative, idempotent, zero false lawful); not cancellative; LE, LT := False. -/
structure BO where v : Bool
instance : OFE BO := OFE.ofDiscrete BO
instance : OFE.Discrete BO := ⟨fun h => h⟩
instance : Inhabited BO := ⟨⟨false⟩⟩
instance : Add BO := ⟨fun a b => ⟨or a.v b.v⟩⟩
instance : Zero BO := ⟨⟨false⟩⟩
instance : LE BO := ⟨fun _ _ => False⟩
instance : LT BO := ⟨fun _ _ => False⟩
instance : Std.Associative (fun (x y : BO) => x + y) := ⟨fun a b c => congrArg BO.mk (Bool.or_assoc a.v b.v c.v)⟩
instance : Std.Commutative (fun (x y : BO) => x + y) := ⟨fun a b => congrArg BO.mk (Bool.or_comm a.v b.v)⟩
instance : Std.IdempotentOp (fun (x y : BO) => x + y) := ⟨fun a => congrArg BO.mk (Bool.or_self a.v)⟩
instance : Std.LeftIdentity (fun (x y : BO) => x + y) (Zero.zero : BO) := ⟨⟩
instance : Std.LawfulLeftIdentity (fun (x y : BO) => x + y) Zero.zero := ⟨fun a => congrArg BO.mk (Bool.false_or a.v)⟩

/-- NA: discrete Nat with +, zero 0: a lawful cancellative commutative monoid. -/
structure NA where v : Nat
instance : OFE NA := OFE.ofDiscrete NA
instance : OFE.Discrete NA := ⟨fun h => h⟩
instance : Add NA := ⟨fun a b => ⟨a.v + b.v⟩⟩
instance : Zero NA := ⟨⟨0⟩⟩
instance : Std.Associative (fun (x y : NA) => x + y) := ⟨fun a b c => congrArg NA.mk (Nat.add_assoc a.v b.v c.v)⟩
instance : Std.Commutative (fun (x y : NA) => x + y) := ⟨fun a b => congrArg NA.mk (Nat.add_comm a.v b.v)⟩
instance : Std.LeftIdentity (fun (x y : NA) => x + y) (Zero.zero : NA) := ⟨⟩
instance : Std.LawfulLeftIdentity (fun (x y : NA) => x + y) Zero.zero := ⟨fun a => congrArg NA.mk (Nat.zero_add a.v)⟩
instance : LeftCancelAdd NA := ⟨fun {x₁ x₂ y} e => by
  cases x₁ with | mk a => cases x₂ with | mk b =>
  have h : y.v + a = y.v + b := congrArg NA.v e
  exact congrArg NA.mk (by omega)⟩

end W3c0

open W3c0

-- `CommMonoidLike.instIsTotal` idx 2: necessary (TA: truncation OFE on Nat (1, 2 agree at step 0) with +, zero 0, left cancellative: not discrete)
theorem w3c0_1 : ¬ indep0% CommMonoidLike.instIsTotal 2 := fun h =>
  ta_nd (@h TA _ _ _ _ _ _)
-- `CommMonoidLike.instIsTotal` idx 4: necessary (L6: commutative cancellative loop of order 6 with identity 0, discrete: not associative)
theorem w3c0_2 : ¬ indep0% CommMonoidLike.instIsTotal 4 := fun h =>
  l6_na (@h L6 _ _ _ _ _ _)
-- `CommMonoidLike.instIsTotal` idx 5: necessary (W1: discrete Nat with x+y=y (associative, idempotent, left cancellative, every element a left identity): not commutative)
theorem w3c0_3 : ¬ indep0% CommMonoidLike.instIsTotal 5 := fun h =>
  w1_nc (@h W1 _ _ _ _ _ _)
-- `CommMonoidLike.instIsTotal` idx 7: necessary (ZN: discrete Nat with + (associative, commutative, left cancellative) and Zero := 1: zero not a left identity)
theorem w3c0_4 : ¬ indep0% CommMonoidLike.instIsTotal 7 := fun h =>
  zn_nl (@h ZN _ _ _ _ _ _)
-- `CommMonoidLike.instDiscrete` idx 2: necessary (TA: truncation OFE on Nat (1, 2 agree at step 0) with +, zero 0, left cancellative: not discrete)
theorem w3c0_5 : ¬ indep0% CommMonoidLike.instDiscrete 2 := fun h =>
  ta_nd (@h TA _ _ _ _ _ _)
-- `CommMonoidLike.instDiscrete` idx 4: necessary (L6: commutative cancellative loop of order 6 with identity 0, discrete: not associative)
theorem w3c0_6 : ¬ indep0% CommMonoidLike.instDiscrete 4 := fun h =>
  l6_na (@h L6 _ _ _ _ _ _)
-- `CommMonoidLike.instDiscrete` idx 5: necessary (W1: discrete Nat with x+y=y (associative, idempotent, left cancellative, every element a left identity): not commutative)
theorem w3c0_7 : ¬ indep0% CommMonoidLike.instDiscrete 5 := fun h =>
  w1_nc (@h W1 _ _ _ _ _ _)
-- `CommMonoidLike.instDiscrete` idx 7: necessary (ZN: discrete Nat with + (associative, commutative, left cancellative) and Zero := 1: zero not a left identity)
theorem w3c0_8 : ¬ indep0% CommMonoidLike.instDiscrete 7 := fun h =>
  zn_nl (@h ZN _ _ _ _ _ _)
-- `CommMonoidLike.instCancelable` idx 2: necessary (TA: truncation OFE on Nat (1, 2 agree at step 0) with +, zero 0, left cancellative: not discrete)
theorem w3c0_9 : ¬ indep0% CommMonoidLike.instCancelable 2 := fun h =>
  ta_nd (@h TA _ _ _ _ _ _ _ default)
-- `CommMonoidLike.instCancelable` idx 5: necessary (W1: discrete Nat with x+y=y (associative, idempotent, left cancellative, every element a left identity): not commutative)
theorem w3c0_10 : ¬ indep0% CommMonoidLike.instCancelable 5 := fun h =>
  w1_nc (@h W1 _ _ _ _ _ _ _ default)
-- `CommMonoidLike.instCancelable` idx 7: necessary (ZN: discrete Nat with + (associative, commutative, left cancellative) and Zero := 1: zero not a left identity)
theorem w3c0_11 : ¬ indep0% CommMonoidLike.instCancelable 7 := fun h =>
  zn_nl (@h ZN _ _ _ _ _ _ _ default)
-- `CommMonoidLike.op_eq` idx 2: necessary (TA: truncation OFE on Nat (1, 2 agree at step 0) with +, zero 0, left cancellative: not discrete)
theorem w3c0_12 : ¬ indep0% CommMonoidLike.op_eq 2 := fun h =>
  ta_nd (@h TA _ _ _ _ _ _ default default)
-- `CommMonoidLike.op_eq` idx 4: necessary (L6: commutative cancellative loop of order 6 with identity 0, discrete: not associative)
theorem w3c0_13 : ¬ indep0% CommMonoidLike.op_eq 4 := fun h =>
  l6_na (@h L6 _ _ _ _ _ _ default default)
-- `CommMonoidLike.op_eq` idx 5: necessary (W1: discrete Nat with x+y=y (associative, idempotent, left cancellative, every element a left identity): not commutative)
theorem w3c0_14 : ¬ indep0% CommMonoidLike.op_eq 5 := fun h =>
  w1_nc (@h W1 _ _ _ _ _ _ default default)
-- `CommMonoidLike.op_eq` idx 7: necessary (ZN: discrete Nat with + (associative, commutative, left cancellative) and Zero := 1: zero not a left identity)
theorem w3c0_15 : ¬ indep0% CommMonoidLike.op_eq 7 := fun h =>
  zn_nl (@h ZN _ _ _ _ _ _ default default)
-- `CommMonoidLike.ord_iff` idx 2: necessary (TA: truncation OFE on Nat (1, 2 agree at step 0) with +, zero 0, left cancellative: not discrete)
theorem w3c0_16 : ¬ indep0% CommMonoidLike.ord_iff 2 := fun h =>
  ta_nd (@h TA _ _ _ _ _ _ default default)
-- `CommMonoidLike.ord_iff` idx 4: necessary (L6: commutative cancellative loop of order 6 with identity 0, discrete: not associative)
theorem w3c0_17 : ¬ indep0% CommMonoidLike.ord_iff 4 := fun h =>
  l6_na (@h L6 _ _ _ _ _ _ default default)
-- `CommMonoidLike.ord_iff` idx 5: necessary (W1: discrete Nat with x+y=y (associative, idempotent, left cancellative, every element a left identity): not commutative)
theorem w3c0_18 : ¬ indep0% CommMonoidLike.ord_iff 5 := fun h =>
  w1_nc (@h W1 _ _ _ _ _ _ default default)
-- `CommMonoidLike.ord_iff` idx 7: necessary (ZN: discrete Nat with + (associative, commutative, left cancellative) and Zero := 1: zero not a left identity)
theorem w3c0_19 : ¬ indep0% CommMonoidLike.ord_iff 7 := fun h =>
  zn_nl (@h ZN _ _ _ _ _ _ default default)
-- `CommMonoidLike.included_iff` idx 2: necessary (TA: truncation OFE on Nat (1, 2 agree at step 0) with +, zero 0, left cancellative: not discrete)
theorem w3c0_20 : ¬ indep0% CommMonoidLike.included_iff 2 := fun h =>
  ta_nd (@h TA _ _ _ _ _ _ default default)
-- `CommMonoidLike.included_iff` idx 4: necessary (L6: commutative cancellative loop of order 6 with identity 0, discrete: not associative)
theorem w3c0_21 : ¬ indep0% CommMonoidLike.included_iff 4 := fun h =>
  l6_na (@h L6 _ _ _ _ _ _ default default)
-- `CommMonoidLike.included_iff` idx 5: necessary (W1: discrete Nat with x+y=y (associative, idempotent, left cancellative, every element a left identity): not commutative)
theorem w3c0_22 : ¬ indep0% CommMonoidLike.included_iff 5 := fun h =>
  w1_nc (@h W1 _ _ _ _ _ _ default default)
-- `CommMonoidLike.included_iff` idx 7: necessary (ZN: discrete Nat with + (associative, commutative, left cancellative) and Zero := 1: zero not a left identity)
theorem w3c0_23 : ¬ indep0% CommMonoidLike.included_iff 7 := fun h =>
  zn_nl (@h ZN _ _ _ _ _ _ default default)
-- `CommMonoidLike.ord_iff_le` idx 2: necessary (TA: truncation OFE on Nat (1, 2 agree at step 0) with +, zero 0, left cancellative: not discrete)
theorem w3c0_24 : ¬ indep0% CommMonoidLike.ord_iff_le 2 := fun h =>
  ta_nd (@h TA _ _ _ _ _ _ _ _ default default)
-- `CommMonoidLike.ord_iff_le` idx 4: necessary (L6: commutative cancellative loop of order 6 with identity 0, discrete: not associative)
theorem w3c0_25 : ¬ indep0% CommMonoidLike.ord_iff_le 4 := fun h =>
  l6_na (@h L6 _ _ _ _ _ _ _ _ default default)
-- `CommMonoidLike.ord_iff_le` idx 7: necessary (ZN: discrete Nat with + (associative, commutative, left cancellative) and Zero := 1: zero not a left identity)
theorem w3c0_26 : ¬ indep0% CommMonoidLike.ord_iff_le 7 := fun h =>
  zn_nl (@h ZN _ _ _ _ _ _ _ _ default default)
-- `CommMonoidLike.inc_iff_le` idx 2: necessary (TA: truncation OFE on Nat (1, 2 agree at step 0) with +, zero 0, left cancellative: not discrete)
theorem w3c0_27 : ¬ indep0% CommMonoidLike.inc_iff_le 2 := fun h =>
  ta_nd (@h TA _ _ _ _ _ _ _ _ default default)
-- `CommMonoidLike.inc_iff_le` idx 4: necessary (L6: commutative cancellative loop of order 6 with identity 0, discrete: not associative)
theorem w3c0_28 : ¬ indep0% CommMonoidLike.inc_iff_le 4 := fun h =>
  l6_na (@h L6 _ _ _ _ _ _ _ _ default default)
-- `CommMonoidLike.inc_iff_le` idx 5: necessary (W1: discrete Nat with x+y=y (associative, idempotent, left cancellative, every element a left identity): not commutative)
theorem w3c0_29 : ¬ indep0% CommMonoidLike.inc_iff_le 5 := fun h =>
  w1_nc (@h W1 _ _ _ _ _ _ _ _ default default)
-- `CommMonoidLike.inc_iff_le` idx 7: necessary (ZN: discrete Nat with + (associative, commutative, left cancellative) and Zero := 1: zero not a left identity)
theorem w3c0_30 : ¬ indep0% CommMonoidLike.inc_iff_le 7 := fun h =>
  zn_nl (@h ZN _ _ _ _ _ _ _ _ default default)
-- `CommMonoidLike.leftCancelAdd_local_update` idx 2: necessary (TA: truncation OFE on Nat (1, 2 agree at step 0) with +, zero 0, left cancellative: not discrete)
theorem w3c0_31 : ¬ indep0% CommMonoidLike.leftCancelAdd_local_update 2 := fun h =>
  ta_nd (@h TA _ _ _ _ _ _ default default default default _ rfl)
-- `CommMonoidLike.leftCancelAdd_local_update` idx 4: necessary (L6: commutative cancellative loop of order 6 with identity 0, discrete: not associative)
theorem w3c0_32 : ¬ indep0% CommMonoidLike.leftCancelAdd_local_update 4 := fun h =>
  l6_na (@h L6 _ _ _ _ _ _ default default default default _ rfl)
-- `CommMonoidLike.leftCancelAdd_local_update` idx 5: necessary (W1: discrete Nat with x+y=y (associative, idempotent, left cancellative, every element a left identity): not commutative)
theorem w3c0_33 : ¬ indep0% CommMonoidLike.leftCancelAdd_local_update 5 := fun h =>
  w1_nc (@h W1 _ _ _ _ _ _ default default default default _ rfl)
-- `CommMonoidLike.leftCancelAdd_local_update` idx 7: necessary (ZN: discrete Nat with + (associative, commutative, left cancellative) and Zero := 1: zero not a left identity)
theorem w3c0_34 : ¬ indep0% CommMonoidLike.leftCancelAdd_local_update 7 := fun h =>
  zn_nl (@h ZN _ _ _ _ _ _ default default default default _ rfl)
-- `CommMonoidLike.instCoreIdZero` idx 2: necessary (TA: truncation OFE on Nat (1, 2 agree at step 0) with +, zero 0, left cancellative: not discrete)
theorem w3c0_35 : ¬ indep0% CommMonoidLike.instCoreIdZero 2 := fun h =>
  ta_nd (@h TA _ _ _ _ _ _)
-- `CommMonoidLike.instCoreIdZero` idx 4: necessary (L6: commutative cancellative loop of order 6 with identity 0, discrete: not associative)
theorem w3c0_36 : ¬ indep0% CommMonoidLike.instCoreIdZero 4 := fun h =>
  l6_na (@h L6 _ _ _ _ _ _)
-- `CommMonoidLike.instCoreIdZero` idx 5: necessary (W1: discrete Nat with x+y=y (associative, idempotent, left cancellative, every element a left identity): not commutative)
theorem w3c0_37 : ¬ indep0% CommMonoidLike.instCoreIdZero 5 := fun h =>
  w1_nc (@h W1 _ _ _ _ _ _)
-- `CommMonoidLike.instCoreIdZero` idx 7: necessary (ZN: discrete Nat with + (associative, commutative, left cancellative) and Zero := 1: zero not a left identity)
theorem w3c0_38 : ¬ indep0% CommMonoidLike.instCoreIdZero 7 := fun h =>
  zn_nl (@h ZN _ _ _ _ _ _)
-- `CommMonoidLike.instIsOp` idx 2: necessary (TA: truncation OFE on Nat (1, 2 agree at step 0) with +, zero 0, left cancellative: not discrete)
theorem w3c0_39 : ¬ indep0% CommMonoidLike.instIsOp 2 := fun h =>
  ta_nd (@h TA _ _ _ _ _ _ .merge default default)
-- `CommMonoidLike.instIsOp` idx 4: necessary (L6: commutative cancellative loop of order 6 with identity 0, discrete: not associative)
theorem w3c0_40 : ¬ indep0% CommMonoidLike.instIsOp 4 := fun h =>
  l6_na (@h L6 _ _ _ _ _ _ .merge default default)
-- `CommMonoidLike.instIsOp` idx 5: necessary (W1: discrete Nat with x+y=y (associative, idempotent, left cancellative, every element a left identity): not commutative)
theorem w3c0_41 : ¬ indep0% CommMonoidLike.instIsOp 5 := fun h =>
  w1_nc (@h W1 _ _ _ _ _ _ .merge default default)
-- `CommMonoidLike.instIsOp` idx 7: necessary (ZN: discrete Nat with + (associative, commutative, left cancellative) and Zero := 1: zero not a left identity)
theorem w3c0_42 : ¬ indep0% CommMonoidLike.instIsOp 7 := fun h =>
  zn_nl (@h ZN _ _ _ _ _ _ .merge default default)
-- `OrdCommMonoidLike.instIsTotal` idx 2: necessary (TX: truncation OFE on Nat with max (associative, commutative, idempotent): not discrete)
theorem w3c0_43 : ¬ indep0% OrdCommMonoidLike.instIsTotal 2 := fun h =>
  tx_nd (@h TX _ _ _ _ _)
-- `OrdCommMonoidLike.instIsTotal` idx 4: necessary (S3: Steiner quasigroup on Fin 3 (2a+2b mod 3; commutative, idempotent, left cancellative), discrete: not associative)
theorem w3c0_44 : ¬ indep0% OrdCommMonoidLike.instIsTotal 4 := fun h =>
  s3_na (@h S3 _ _ _ _ _)
-- `OrdCommMonoidLike.instIsTotal` idx 5: necessary (W1: discrete Nat with x+y=y (associative, idempotent, left cancellative): not commutative)
theorem w3c0_45 : ¬ indep0% OrdCommMonoidLike.instIsTotal 5 := fun h =>
  w1_nc (@h W1 _ _ _ _ _)
-- `OrdCommMonoidLike.instIsTotal` idx 6: necessary (ZN: discrete Nat with + (associative, commutative, left cancellative): 1+1 ≠ 1, not idempotent)
theorem w3c0_46 : ¬ indep0% OrdCommMonoidLike.instIsTotal 6 := fun h =>
  zn_ni (@h ZN _ _ _ _ _)
-- `OrdCommMonoidLike.instDiscrete` idx 2: necessary (TX: truncation OFE on Nat with max (associative, commutative, idempotent): not discrete)
theorem w3c0_47 : ¬ indep0% OrdCommMonoidLike.instDiscrete 2 := fun h =>
  tx_nd (@h TX _ _ _ _ _)
-- `OrdCommMonoidLike.instDiscrete` idx 4: necessary (S3: Steiner quasigroup on Fin 3 (2a+2b mod 3; commutative, idempotent, left cancellative), discrete: not associative)
theorem w3c0_48 : ¬ indep0% OrdCommMonoidLike.instDiscrete 4 := fun h =>
  s3_na (@h S3 _ _ _ _ _)
-- `OrdCommMonoidLike.instDiscrete` idx 5: necessary (W1: discrete Nat with x+y=y (associative, idempotent, left cancellative): not commutative)
theorem w3c0_49 : ¬ indep0% OrdCommMonoidLike.instDiscrete 5 := fun h =>
  w1_nc (@h W1 _ _ _ _ _)
-- `OrdCommMonoidLike.instDiscrete` idx 6: necessary (ZN: discrete Nat with + (associative, commutative, left cancellative): 1+1 ≠ 1, not idempotent)
theorem w3c0_50 : ¬ indep0% OrdCommMonoidLike.instDiscrete 6 := fun h =>
  zn_ni (@h ZN _ _ _ _ _)
-- `OrdCommMonoidLike.instCoreId` idx 2: necessary (TX: truncation OFE on Nat with max (associative, commutative, idempotent): not discrete)
theorem w3c0_51 : ¬ indep0% OrdCommMonoidLike.instCoreId 2 := fun h =>
  tx_nd (@h TX _ _ _ _ _ default)
-- `OrdCommMonoidLike.instCoreId` idx 4: necessary (S3: Steiner quasigroup on Fin 3 (2a+2b mod 3; commutative, idempotent, left cancellative), discrete: not associative)
theorem w3c0_52 : ¬ indep0% OrdCommMonoidLike.instCoreId 4 := fun h =>
  s3_na (@h S3 _ _ _ _ _ default)
-- `OrdCommMonoidLike.instCoreId` idx 5: necessary (W1: discrete Nat with x+y=y (associative, idempotent, left cancellative): not commutative)
theorem w3c0_53 : ¬ indep0% OrdCommMonoidLike.instCoreId 5 := fun h =>
  w1_nc (@h W1 _ _ _ _ _ default)
-- `OrdCommMonoidLike.instCoreId` idx 6: necessary (ZN: discrete Nat with + (associative, commutative, left cancellative): 1+1 ≠ 1, not idempotent)
theorem w3c0_54 : ¬ indep0% OrdCommMonoidLike.instCoreId 6 := fun h =>
  zn_ni (@h ZN _ _ _ _ _ default)
-- `OrdCommMonoidLike.instCancelable` idx 4: necessary (S3: Steiner quasigroup on Fin 3 (2a+2b mod 3; commutative, idempotent, left cancellative), discrete: not associative)
theorem w3c0_55 : ¬ indep0% OrdCommMonoidLike.instCancelable 4 := fun h =>
  s3_na (@h S3 _ _ _ _ _ _ default)
-- `OrdCommMonoidLike.instCancelable` idx 5: necessary (W1: discrete Nat with x+y=y (associative, idempotent, left cancellative): not commutative)
theorem w3c0_56 : ¬ indep0% OrdCommMonoidLike.instCancelable 5 := fun h =>
  w1_nc (@h W1 _ _ _ _ _ _ default)
-- `OrdCommMonoidLike.instCancelable` idx 6: necessary (ZN: discrete Nat with + (associative, commutative, left cancellative): 1+1 ≠ 1, not idempotent)
theorem w3c0_57 : ¬ indep0% OrdCommMonoidLike.instCancelable 6 := fun h =>
  zn_ni (@h ZN _ _ _ _ _ _ default)
-- `OrdCommMonoidLike.op_eq` idx 2: necessary (TX: truncation OFE on Nat with max (associative, commutative, idempotent): not discrete)
theorem w3c0_58 : ¬ indep0% OrdCommMonoidLike.op_eq 2 := fun h =>
  tx_nd (@h TX _ _ _ _ _ default default)
-- `OrdCommMonoidLike.op_eq` idx 4: necessary (S3: Steiner quasigroup on Fin 3 (2a+2b mod 3; commutative, idempotent, left cancellative), discrete: not associative)
theorem w3c0_59 : ¬ indep0% OrdCommMonoidLike.op_eq 4 := fun h =>
  s3_na (@h S3 _ _ _ _ _ default default)
-- `OrdCommMonoidLike.op_eq` idx 5: necessary (W1: discrete Nat with x+y=y (associative, idempotent, left cancellative): not commutative)
theorem w3c0_60 : ¬ indep0% OrdCommMonoidLike.op_eq 5 := fun h =>
  w1_nc (@h W1 _ _ _ _ _ default default)
-- `OrdCommMonoidLike.op_eq` idx 6: necessary (ZN: discrete Nat with + (associative, commutative, left cancellative): 1+1 ≠ 1, not idempotent)
theorem w3c0_61 : ¬ indep0% OrdCommMonoidLike.op_eq 6 := fun h =>
  zn_ni (@h ZN _ _ _ _ _ default default)
-- `OrdCommMonoidLike.ord_iff` idx 2: necessary (TX: truncation OFE on Nat with max (associative, commutative, idempotent): not discrete)
theorem w3c0_62 : ¬ indep0% OrdCommMonoidLike.ord_iff 2 := fun h =>
  tx_nd (@h TX _ _ _ _ _ default default)
-- `OrdCommMonoidLike.ord_iff` idx 4: necessary (S3: Steiner quasigroup on Fin 3 (2a+2b mod 3; commutative, idempotent, left cancellative), discrete: not associative)
theorem w3c0_63 : ¬ indep0% OrdCommMonoidLike.ord_iff 4 := fun h =>
  s3_na (@h S3 _ _ _ _ _ default default)
-- `OrdCommMonoidLike.ord_iff` idx 5: necessary (W1: discrete Nat with x+y=y (associative, idempotent, left cancellative): not commutative)
theorem w3c0_64 : ¬ indep0% OrdCommMonoidLike.ord_iff 5 := fun h =>
  w1_nc (@h W1 _ _ _ _ _ default default)
-- `OrdCommMonoidLike.ord_iff` idx 6: necessary (ZN: discrete Nat with + (associative, commutative, left cancellative): 1+1 ≠ 1, not idempotent)
theorem w3c0_65 : ¬ indep0% OrdCommMonoidLike.ord_iff 6 := fun h =>
  zn_ni (@h ZN _ _ _ _ _ default default)
-- `OrdCommMonoidLike.inc_iff` idx 2: necessary (TX: truncation OFE on Nat with max (associative, commutative, idempotent): not discrete)
theorem w3c0_66 : ¬ indep0% OrdCommMonoidLike.inc_iff 2 := fun h =>
  tx_nd (@h TX _ _ _ _ _ default default)
-- `OrdCommMonoidLike.inc_iff` idx 4: necessary (S3: Steiner quasigroup on Fin 3 (2a+2b mod 3; commutative, idempotent, left cancellative), discrete: not associative)
theorem w3c0_67 : ¬ indep0% OrdCommMonoidLike.inc_iff 4 := fun h =>
  s3_na (@h S3 _ _ _ _ _ default default)
-- `OrdCommMonoidLike.inc_iff` idx 5: necessary (W1: discrete Nat with x+y=y (associative, idempotent, left cancellative): not commutative)
theorem w3c0_68 : ¬ indep0% OrdCommMonoidLike.inc_iff 5 := fun h =>
  w1_nc (@h W1 _ _ _ _ _ default default)
-- `OrdCommMonoidLike.inc_iff` idx 6: necessary (ZN: discrete Nat with + (associative, commutative, left cancellative): 1+1 ≠ 1, not idempotent)
theorem w3c0_69 : ¬ indep0% OrdCommMonoidLike.inc_iff 6 := fun h =>
  zn_ni (@h ZN _ _ _ _ _ default default)
-- `OrdCommMonoidLike.idem_local_update_ord` idx 2: necessary (TX: truncation OFE on Nat with max (associative, commutative, idempotent): not discrete)
theorem w3c0_70 : ¬ indep0% OrdCommMonoidLike.idem_local_update_ord 2 := fun h =>
  tx_nd (@h TX _ _ _ _ _ default default default)
-- `OrdCommMonoidLike.idem_local_update_ord` idx 4: necessary (S3: Steiner quasigroup on Fin 3 (2a+2b mod 3; commutative, idempotent, left cancellative), discrete: not associative)
theorem w3c0_71 : ¬ indep0% OrdCommMonoidLike.idem_local_update_ord 4 := fun h =>
  s3_na (@h S3 _ _ _ _ _ default default default)
-- `OrdCommMonoidLike.idem_local_update_ord` idx 5: necessary (W1: discrete Nat with x+y=y (associative, idempotent, left cancellative): not commutative)
theorem w3c0_72 : ¬ indep0% OrdCommMonoidLike.idem_local_update_ord 5 := fun h =>
  w1_nc (@h W1 _ _ _ _ _ default default default)
-- `OrdCommMonoidLike.idem_local_update_ord` idx 6: necessary (ZN: discrete Nat with + (associative, commutative, left cancellative): 1+1 ≠ 1, not idempotent)
theorem w3c0_73 : ¬ indep0% OrdCommMonoidLike.idem_local_update_ord 6 := fun h =>
  zn_ni (@h ZN _ _ _ _ _ default default default)
-- `OrdCommMonoidLike.idem_local_update` idx 2: necessary (TX: truncation OFE on Nat with max (associative, commutative, idempotent): not discrete)
theorem w3c0_74 : ¬ indep0% OrdCommMonoidLike.idem_local_update 2 := fun h =>
  tx_nd (@h TX _ _ _ _ _ default default default)
-- `OrdCommMonoidLike.idem_local_update` idx 4: necessary (S3: Steiner quasigroup on Fin 3 (2a+2b mod 3; commutative, idempotent, left cancellative), discrete: not associative)
theorem w3c0_75 : ¬ indep0% OrdCommMonoidLike.idem_local_update 4 := fun h =>
  s3_na (@h S3 _ _ _ _ _ default default default)
-- `OrdCommMonoidLike.idem_local_update` idx 5: necessary (W1: discrete Nat with x+y=y (associative, idempotent, left cancellative): not commutative)
theorem w3c0_76 : ¬ indep0% OrdCommMonoidLike.idem_local_update 5 := fun h =>
  w1_nc (@h W1 _ _ _ _ _ default default default)
-- `OrdCommMonoidLike.idem_local_update` idx 6: necessary (ZN: discrete Nat with + (associative, commutative, left cancellative): 1+1 ≠ 1, not idempotent)
theorem w3c0_77 : ¬ indep0% OrdCommMonoidLike.idem_local_update 6 := fun h =>
  zn_ni (@h ZN _ _ _ _ _ default default default)
-- `PosCommMonoidLike.instDiscrete` idx 2: necessary (TP: truncation OFE on Nat with a+b+1 (associative, commutative, identity free): not discrete)
theorem w3c0_78 : ¬ indep0% PosCommMonoidLike.instDiscrete 2 := fun h =>
  tp_nd (@h TP _ _ _ _)
-- `PosCommMonoidLike.instDiscrete` idx 4: necessary (NQ: discrete Nat with a*b+a+b+1 (commutative, left cancellative, identity free): not associative)
theorem w3c0_79 : ¬ indep0% PosCommMonoidLike.instDiscrete 4 := fun h =>
  nq_na (@h NQ _ _ _ _)
-- `PosCommMonoidLike.instDiscrete` idx 5: necessary (LW: discrete Bool lists with a ++ true :: b (associative, left cancellative, identity free): not commutative)
theorem w3c0_80 : ¬ indep0% PosCommMonoidLike.instDiscrete 5 := fun h =>
  lw_nc (@h LW _ _ _ _)
-- `PosCommMonoidLike.instCancelable` idx 4: necessary (NQ: discrete Nat with a*b+a+b+1 (commutative, left cancellative, identity free): not associative)
theorem w3c0_81 : ¬ indep0% PosCommMonoidLike.instCancelable 4 := fun h =>
  nq_na (@h NQ _ _ _ _ _ default)
-- `PosCommMonoidLike.instCancelable` idx 5: necessary (LW: discrete Bool lists with a ++ true :: b (associative, left cancellative, identity free): not commutative)
theorem w3c0_82 : ¬ indep0% PosCommMonoidLike.instCancelable 5 := fun h =>
  lw_nc (@h LW _ _ _ _ _ default)
-- `PosCommMonoidLike.instIdFree` idx 2: necessary (TP: truncation OFE on Nat with a+b+1 (associative, commutative, identity free): not discrete)
theorem w3c0_83 : ¬ indep0% PosCommMonoidLike.instIdFree 2 := fun h =>
  tp_nd (@h TP _ _ _ _ _ default)
-- `PosCommMonoidLike.instIdFree` idx 4: necessary (NQ: discrete Nat with a*b+a+b+1 (commutative, left cancellative, identity free): not associative)
theorem w3c0_84 : ¬ indep0% PosCommMonoidLike.instIdFree 4 := fun h =>
  nq_na (@h NQ _ _ _ _ _ default)
-- `PosCommMonoidLike.instIdFree` idx 5: necessary (LW: discrete Bool lists with a ++ true :: b (associative, left cancellative, identity free): not commutative)
theorem w3c0_85 : ¬ indep0% PosCommMonoidLike.instIdFree 5 := fun h =>
  lw_nc (@h LW _ _ _ _ _ default)
-- `PosCommMonoidLike.op_eq` idx 2: necessary (TP: truncation OFE on Nat with a+b+1 (associative, commutative, identity free): not discrete)
theorem w3c0_86 : ¬ indep0% PosCommMonoidLike.op_eq 2 := fun h =>
  tp_nd (@h TP _ _ _ _ default default)
-- `PosCommMonoidLike.op_eq` idx 4: necessary (NQ: discrete Nat with a*b+a+b+1 (commutative, left cancellative, identity free): not associative)
theorem w3c0_87 : ¬ indep0% PosCommMonoidLike.op_eq 4 := fun h =>
  nq_na (@h NQ _ _ _ _ default default)
-- `PosCommMonoidLike.op_eq` idx 5: necessary (LW: discrete Bool lists with a ++ true :: b (associative, left cancellative, identity free): not commutative)
theorem w3c0_88 : ¬ indep0% PosCommMonoidLike.op_eq 5 := fun h =>
  lw_nc (@h LW _ _ _ _ default default)
-- `PosCommMonoidLike.ord_iff` idx 2: necessary (TP: truncation OFE on Nat with a+b+1 (associative, commutative, identity free): not discrete)
theorem w3c0_89 : ¬ indep0% PosCommMonoidLike.ord_iff 2 := fun h =>
  tp_nd (@h TP _ _ _ _ default default)
-- `PosCommMonoidLike.ord_iff` idx 4: necessary (NQ: discrete Nat with a*b+a+b+1 (commutative, left cancellative, identity free): not associative)
theorem w3c0_90 : ¬ indep0% PosCommMonoidLike.ord_iff 4 := fun h =>
  nq_na (@h NQ _ _ _ _ default default)
-- `PosCommMonoidLike.ord_iff` idx 5: necessary (LW: discrete Bool lists with a ++ true :: b (associative, left cancellative, identity free): not commutative)
theorem w3c0_91 : ¬ indep0% PosCommMonoidLike.ord_iff 5 := fun h =>
  lw_nc (@h LW _ _ _ _ default default)
-- `PosCommMonoidLike.included_iff` idx 2: necessary (TP: truncation OFE on Nat with a+b+1 (associative, commutative, identity free): not discrete)
theorem w3c0_92 : ¬ indep0% PosCommMonoidLike.included_iff 2 := fun h =>
  tp_nd (@h TP _ _ _ _ default default)
-- `PosCommMonoidLike.included_iff` idx 4: necessary (NQ: discrete Nat with a*b+a+b+1 (commutative, left cancellative, identity free): not associative)
theorem w3c0_93 : ¬ indep0% PosCommMonoidLike.included_iff 4 := fun h =>
  nq_na (@h NQ _ _ _ _ default default)
-- `PosCommMonoidLike.included_iff` idx 5: necessary (LW: discrete Bool lists with a ++ true :: b (associative, left cancellative, identity free): not commutative)
theorem w3c0_94 : ¬ indep0% PosCommMonoidLike.included_iff 5 := fun h =>
  lw_nc (@h LW _ _ _ _ default default)
-- `PosCommMonoidLike.ord_iff_lt` idx 2: necessary (TP: truncation OFE on Nat with a+b+1 (associative, commutative, identity free): not discrete)
theorem w3c0_95 : ¬ indep0% PosCommMonoidLike.ord_iff_lt 2 := fun h =>
  tp_nd (@h TP _ _ _ _ _ _ default default)
-- `PosCommMonoidLike.ord_iff_lt` idx 4: necessary (NQ: discrete Nat with a*b+a+b+1 (commutative, left cancellative, identity free): not associative)
theorem w3c0_96 : ¬ indep0% PosCommMonoidLike.ord_iff_lt 4 := fun h =>
  nq_na (@h NQ _ _ _ _ _ _ default default)
-- `PosCommMonoidLike.ord_iff_lt` idx 5: necessary (LW: discrete Bool lists with a ++ true :: b (associative, left cancellative, identity free): not commutative)
theorem w3c0_97 : ¬ indep0% PosCommMonoidLike.ord_iff_lt 5 := fun h =>
  lw_nc (@h LW _ _ _ _ _ _ default default)
-- `PosCommMonoidLike.inc_iff_lt` idx 2: necessary (TP: truncation OFE on Nat with a+b+1 (associative, commutative, identity free): not discrete)
theorem w3c0_98 : ¬ indep0% PosCommMonoidLike.inc_iff_lt 2 := fun h =>
  tp_nd (@h TP _ _ _ _ _ _ default default)
-- `PosCommMonoidLike.inc_iff_lt` idx 4: necessary (NQ: discrete Nat with a*b+a+b+1 (commutative, left cancellative, identity free): not associative)
theorem w3c0_99 : ¬ indep0% PosCommMonoidLike.inc_iff_lt 4 := fun h =>
  nq_na (@h NQ _ _ _ _ _ _ default default)
-- `PosCommMonoidLike.inc_iff_lt` idx 5: necessary (LW: discrete Bool lists with a ++ true :: b (associative, left cancellative, identity free): not commutative)
theorem w3c0_100 : ¬ indep0% PosCommMonoidLike.inc_iff_lt 5 := fun h =>
  lw_nc (@h LW _ _ _ _ _ _ default default)
-- `PosCommMonoidLike.instIsOp` idx 2: necessary (TP: truncation OFE on Nat with a+b+1 (associative, commutative, identity free): not discrete)
theorem w3c0_101 : ¬ indep0% PosCommMonoidLike.instIsOp 2 := fun h =>
  tp_nd (@h TP _ _ _ _ .merge default default)
-- `PosCommMonoidLike.instIsOp` idx 4: necessary (NQ: discrete Nat with a*b+a+b+1 (commutative, left cancellative, identity free): not associative)
theorem w3c0_102 : ¬ indep0% PosCommMonoidLike.instIsOp 4 := fun h =>
  nq_na (@h NQ _ _ _ _ .merge default default)
-- `PosCommMonoidLike.instIsOp` idx 5: necessary (LW: discrete Bool lists with a ++ true :: b (associative, left cancellative, identity free): not commutative)
theorem w3c0_103 : ¬ indep0% PosCommMonoidLike.instIsOp 5 := fun h =>
  lw_nc (@h LW _ _ _ _ .merge default default)

-- `LeftCancelAdd.cancel_left` idx 2: necessary (Bool with or: true + true = true + false)
theorem w3c0_n1 : ¬ drop0% LeftCancelAdd.cancel_left 2 := fun h =>
  absurd (@h Bool ⟨fun a b => or a b⟩ true false true rfl) (by decide)
-- `LeftCancelAdd.cancel_right` idx 5: necessary (Bool with or, commutative: true + true = false + true)
theorem w3c0_n2 : ¬ drop0% LeftCancelAdd.cancel_right 5 := fun h =>
  absurd (@h Bool true false true ⟨fun a b => or a b⟩ ⟨fun a b => Bool.or_comm a b⟩ rfl) (by decide)
-- `LeftCancelAdd.cancel_right` idx 6: necessary (W1, x+y=y, left cancellative: 1+0 = 2+0)
theorem w3c0_n3 : ¬ drop0% LeftCancelAdd.cancel_right 6 := fun h =>
  absurd (congrArg W1.v (@h W1 ⟨1⟩ ⟨2⟩ ⟨0⟩ _ _ rfl)) (by decide)
-- `CommMonoidLike.instCancelable` idx 8: necessary (BO, Bool with or: true • true = true • false, true not cancelable)
theorem w3c0_n4 : ¬ drop0% CommMonoidLike.instCancelable 8 := fun h => by
  have := (@h BO _ _ _ _ _ _ _ ⟨true⟩).cancelableN (n := 0) (y := ⟨true⟩) (z := ⟨false⟩) trivial rfl
  have h2 : (⟨true⟩ : BO) = ⟨false⟩ := this
  cases h2
-- `CommMonoidLike.ord_iff_le` idx 9: necessary (BO with LE := False: false ≼ₒ false via z = false)
theorem w3c0_n5 : ¬ drop0% CommMonoidLike.ord_iff_le 9 := fun h =>
  (@h BO _ _ _ _ _ _ _ _ ⟨false⟩ ⟨false⟩).mp ⟨⟨false⟩, rfl⟩
-- `CommMonoidLike.inc_iff_le` idx 9: necessary (BO with LE := False: false ≼ false)
theorem w3c0_n6 : ¬ drop0% CommMonoidLike.inc_iff_le 9 := fun h =>
  (@h BO _ _ _ _ _ _ _ _ ⟨false⟩ ⟨false⟩).mp ⟨⟨false⟩, by first | rfl | exact OFE.Equiv.rfl | exact fun _ => rfl⟩
-- `CommMonoidLike.leftCancelAdd_local_update` idx 12: necessary (BO: x=y=x'=true, y'=false satisfy x+y'=x'+y; with mz = none x ≡ y but x' ≢ y')
theorem w3c0_n7 : ¬ drop0% CommMonoidLike.leftCancelAdd_local_update 12 := fun h => by
  have := (@h BO _ _ _ _ _ _ _ ⟨true⟩ ⟨true⟩ ⟨true⟩ ⟨false⟩ rfl 0 none trivial rfl).2
  have h2 : (⟨true⟩ : BO) = ⟨false⟩ := this
  cases h2
-- `CommMonoidLike.leftCancelAdd_local_update` idx 13: necessary (NA, Nat with +: (0,0) ~l~> (1,0) fails at mz = none)
theorem w3c0_n8 : ¬ drop0% CommMonoidLike.leftCancelAdd_local_update 13 := fun h => by
  have := (@h NA _ _ _ _ _ _ _ ⟨0⟩ ⟨0⟩ ⟨1⟩ ⟨0⟩ _ 0 none trivial rfl).2
  have h2 : (⟨1⟩ : NA) = ⟨0⟩ := this
  cases h2
-- `CommMonoidLike.instDiscreteE` idx 2: necessary (TA truncation OFE: 1 and 2 agree at step 0)
theorem w3c0_n9 : ¬ drop0% CommMonoidLike.instDiscreteE 2 := fun h => ta_nde (@h TA _ ⟨1⟩)
-- `OrdCommMonoidLike.instDiscreteE` idx 2: necessary (TA truncation OFE: 1 and 2 agree at step 0)
theorem w3c0_n10 : ¬ drop0% OrdCommMonoidLike.instDiscreteE 2 := fun h => ta_nde (@h TA _ ⟨1⟩)
-- `OrdCommMonoidLike.instCancelable` idx 7: necessary (BO, Bool with or: true not cancelable)
theorem w3c0_n11 : ¬ drop0% OrdCommMonoidLike.instCancelable 7 := fun h => by
  have := (@h BO _ _ _ _ _ _ ⟨true⟩).cancelableN (n := 0) (y := ⟨true⟩) (z := ⟨false⟩) trivial rfl
  have h2 : (⟨true⟩ : BO) = ⟨false⟩ := this
  cases h2
-- `OrdCommMonoidLike.idem_local_update_ord` idx 10: necessary (BO: x=true, y=false, x'=false, mz = some true: false ≢ false • true)
theorem w3c0_n12 : ¬ drop0% OrdCommMonoidLike.idem_local_update_ord 10 := fun h => by
  have := (@h BO _ _ _ _ _ _ ⟨true⟩ ⟨false⟩ ⟨false⟩ 0 (some ⟨true⟩) trivial rfl).2
  have h2 : (⟨false⟩ : BO) = ⟨true⟩ := this
  cases h2
-- `OrdCommMonoidLike.idem_local_update` idx 10: necessary (BO: x=true, y=false, x'=false, mz = some true: false ≢ false • true)
theorem w3c0_n13 : ¬ drop0% OrdCommMonoidLike.idem_local_update 10 := fun h => by
  have := (@h BO _ _ _ _ _ _ ⟨true⟩ ⟨false⟩ ⟨false⟩ 0 (some ⟨true⟩) trivial rfl).2
  have h2 : (⟨false⟩ : BO) = ⟨true⟩ := this
  cases h2
-- `PosCommMonoidLike.instCancelable` idx 6: necessary (BO, Bool with or: true not cancelable)
theorem w3c0_n14 : ¬ drop0% PosCommMonoidLike.instCancelable 6 := fun h => by
  have := (@h BO _ _ _ _ _ ⟨true⟩).cancelableN (n := 0) (y := ⟨true⟩) (z := ⟨false⟩) trivial rfl
  have h2 : (⟨true⟩ : BO) = ⟨false⟩ := this
  cases h2
-- `PosCommMonoidLike.instIdFree` idx 6: necessary (BO, Bool with or: true • false = true)
theorem w3c0_n15 : ¬ drop0% PosCommMonoidLike.instIdFree 6 := fun h =>
  (@h BO _ _ _ _ _ ⟨true⟩).id_free0_r ⟨false⟩ trivial rfl
-- `PosCommMonoidLike.ord_iff_lt` idx 7: necessary (BO with LT := False: false ≼ₒ false)
theorem w3c0_n16 : ¬ drop0% PosCommMonoidLike.ord_iff_lt 7 := fun h =>
  (@h BO _ _ _ _ _ _ ⟨false⟩ ⟨false⟩).mp ⟨⟨false⟩, rfl⟩
-- `PosCommMonoidLike.inc_iff_lt` idx 7: necessary (BO with LT := False: false ≼ false)
theorem w3c0_n17 : ¬ drop0% PosCommMonoidLike.inc_iff_lt 7 := fun h =>
  (@h BO _ _ _ _ _ _ ⟨false⟩ ⟨false⟩).mp ⟨⟨false⟩, by first | rfl | exact OFE.Equiv.rfl | exact fun _ => rfl⟩
-- `Iris.MaxNat.local_update` idx 3: necessary (a=1, b=0, a'=0, mz = some 1: 1 = max 0 1 but 0 ≠ max 0 1)
theorem w3c0_n18 : ¬ drop0% Iris.MaxNat.local_update 3 := fun h => by
  have := (@h (.ofNat 1) (.ofNat 0) (.ofNat 0) 0 (some (.ofNat 1)) trivial rfl).2
  have h2 : Iris.MaxNat.ofNat 0 = Iris.MaxNat.ofNat 1 := this
  exact absurd (congrArg Iris.MaxNat.toNat h2) (by decide)
-- `Iris.MaxInt.local_update` idx 3: necessary (a=1, b=0, a'=0, mz = some 1: 1 = max 0 1 but 0 ≠ max 0 1)
theorem w3c0_n19 : ¬ drop0% Iris.MaxInt.local_update 3 := fun h => by
  have := (@h (.ofInt 1) (.ofInt 0) (.ofInt 0) 0 (some (.ofInt 1)) trivial rfl).2
  have h2 : Iris.MaxInt.ofInt 0 = Iris.MaxInt.ofInt 1 := this
  exact absurd (congrArg Iris.MaxInt.toInt h2) (by decide)
-- `Iris.MinNat.local_update` idx 3: necessary (a=0, b=1, a'=1, mz = some 0: 0 = min 1 0 but 1 ≠ min 1 0)
theorem w3c0_n20 : ¬ drop0% Iris.MinNat.local_update 3 := fun h => by
  have := (@h (.ofNat 0) (.ofNat 1) (.ofNat 1) 0 (some (.ofNat 0)) trivial rfl).2
  have h2 : Iris.MinNat.ofNat 1 = Iris.MinNat.ofNat 0 := this
  exact absurd (congrArg Iris.MinNat.toNat h2) (by decide)
-- `OrdCommMonoidLike.instCancelable` idx 2: removable (derivable: left cancellation plus idempotence and commutativity force y + x = x = x + y, so the type is a subsingleton and trivially discrete)
theorem w3c0_r1 : indep% OrdCommMonoidLike.instCancelable 2 := by
  intro α _ _ hA hC hI hL _
  have key : ∀ x y : α, y + x = x := fun x y =>
    hL.cancel_left (y := y) (by
      have e1 := hA.assoc y y x
      have e2 := hI.idempotent y
      rw [← e1, e2])
  exact ⟨fun {x y} _ => by
    have h1 := key x y
    have h2 := key y x
    have h3 := hC.comm x y
    rw [← h1, ← h3, h2]⟩
