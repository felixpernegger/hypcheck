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

namespace W4c2
open Iris Iris.BI Iris.Std Iris.Algebra Iris.Instances.Classical Iris.Instances.Data

-- helper
abbrev TM := fun V => Std.ExtTreeMap Nat V compare
-- helper
theorem sp {P Q : SiProp} (h : P ⊢ Q) (n : Nat) : P.holds n → Q.holds n := h n
-- helper
def h0 : State Unit := fun i => if i = 0 then result () else unknown
-- helper
theorem h0_ne : h0 ≠ ∅ := fun h => by
  have := congrFun h 0; simp [h0, EmptyCollection.emptyCollection] at this
-- helper
def own0 : HeapProp Unit := fun σ => σ 0 ≠ unknown
-- helper
theorem hp {P Q : HeapProp Unit} (h : P ⊢ Q) (σ : State Unit) : P σ → Q σ := h σ
-- helper
theorem not_true_emp (h : iprop(True) ⊢ (emp : HeapProp Unit)) : False := h0_ne (h h0 trivial)
-- helper
theorem own0_sep_own0 {σ : State Unit} : ¬ iprop(own0 ∗ own0) σ := fun ⟨σ1, σ2, _, hd, h1, h2⟩ =>
  (hd 0).elim h1 h2
-- helper
theorem own0_h0 : own0 h0 := by simp [own0, h0]
-- helper: one-key map
abbrev sg {V : Type} (v : V) : TM V := PartialMap.insert ∅ 0 v
-- helper
theorem sg_get {V : Type} (v : V) : get? (sg v) 0 = some v := get?_insert_eq rfl
-- helper
theorem sgE {PROP : Type _} [BI PROP] {V : Type} (Φ : Nat → V → PROP) (v : V) :
    bigSepM Φ (sg v) = Φ 0 v := BigOpM.bigOpM_singleton_eq (op := BIBase.sep) Φ 0 v
-- helper
theorem emE {PROP : Type _} [BI PROP] {V : Type} (Φ : Nat → V → PROP) :
    bigSepM Φ (∅ : TM V) = emp := BigOpM.bigOpM_empty (op := BIBase.sep) Φ

-- helper
theorem insIns {V : Type} (a b : V) : PartialMap.insert (sg a) 0 b = sg b :=
  equiv_iff_eq.mp fun k => by
    by_cases hk : 0 = k
    · rw [get?_insert_eq hk, get?_insert_eq hk]
    · rw [get?_insert_ne hk, get?_insert_ne hk, get?_insert_ne hk]
-- helper
theorem unionSelf {M' : Type → Type} {K V : Type} [LawfulPartialMap M' K] (m : M' V) : m ∪ m = m :=
  equiv_iff_eq.mp fun k => by
    rw [LawfulPartialMap.get?_union]; cases get? m k <;> rfl
-- helper
theorem zw {A B C : Type} (f : A → B → C) (a : A) (b : B) :
    PartialMap.zipWith f (sg a) (sg b) = sg (f a b) :=
  equiv_iff_eq.mp fun k => by
    rw [LawfulPartialMap.get?_zipWith]
    by_cases hk : 0 = k
    · rw [get?_insert_eq hk, get?_insert_eq hk, get?_insert_eq hk]; rfl
    · rw [get?_insert_ne hk, get?_insert_ne hk, get?_insert_ne hk, get?_empty, get?_empty, get?_empty]; rfl
-- helper
theorem domSg {A B : Type} (a : A) (b : B) (k : Nat) :
    (get? (sg a) k).isSome = true ↔ (get? (sg b) k).isSome = true := by
  by_cases hk : 0 = k
  · rw [get?_insert_eq hk, get?_insert_eq hk]; rfl
  · rw [get?_insert_ne hk, get?_insert_ne hk, get?_empty, get?_empty]; exact Iff.rfl
-- helper
theorem ofListU (L : List (Nat × Unit)) (hL : ∀ e ∈ L, e.1 = 0) (hne : L ≠ []) :
    (PartialMap.ofList L : TM Unit) = sg () := by
  induction L with
  | nil => exact absurd rfl hne
  | cons e L ih =>
    obtain ⟨k, u⟩ := e
    have hk : k = 0 := hL _ (List.mem_cons_self ..)
    subst hk
    cases L with
    | nil => rfl
    | cons e' L' =>
      rw [LawfulPartialMap.ofList_cons, ih (fun e he => hL e (List.mem_cons_of_mem _ he)) (List.cons_ne_nil _ _), insIns]
-- helper: SiProp true only at step 0 (not timeless)
def s0 : SiProp := ⟨fun n => n = 0, fun h hle => by omega⟩
-- helper
theorem s0_not_timeless {Q : SiProp} (e : Q ⊣⊢ s0) (h : ▷ Q ⊢ ◇ Q) : False := by
  have := ((later_mono e.2).trans (h.trans (except0_mono e.1))) 1 rfl
  rcases this with h1 | h1
  · exact h1
  · exact absurd h1 (by simp [s0])
-- helper
theorem hcast {P Q : SiProp} (e : P = Q) (h : P.holds 0) : Q.holds 0 := e ▸ h
-- helper: two-key map
abbrev tw {V : Type} (a b : V) : TM V := PartialMap.insert (sg a) 1 b
-- helper
theorem twE {PROP : Type _} [BI PROP] {V : Type} (Φ : Nat → V → PROP) (a b : V) :
    bigSepM Φ (tw a b) = iprop(Φ 1 b ∗ Φ 0 a) :=
  (BigOpM.bigOpM_insert_eq (op := BIBase.sep) Φ b ((get?_insert_ne (by decide)).trans (get?_empty 1))).trans
    (congrArg (BIBase.sep (Φ 1 b)) (sgE Φ a))
-- helper
theorem zwE {A B C : Type} (f : A → B → C) (a : A) :
    PartialMap.zipWith f (sg a) (∅ : TM B) = ∅ :=
  equiv_iff_eq.mp fun k => by
    rw [LawfulPartialMap.get?_zipWith, get?_empty]
    cases get? (sg a) k <;> rfl
-- helper
theorem s2E {PROP : Type _} [BI PROP] {A B : Type} (Φ : Nat → A → B → PROP) (a : A) (b : B) :
    bigSepM2 Φ (sg a) (sg b) ⊣⊢ Φ 0 a b := BigSepM2.bigSepM2_singleton Φ 0 a b
-- helper
theorem sg_ne {V : Type} (v : V) : sg v ≠ ∅ := LawfulPartialMap.singleton_ne_empty
-- helper: a trivial equivalence on Unit
instance ueq : HasEquiv Unit := ⟨fun _ _ => True⟩
-- helper
theorem orelU (o : Option Unit) : Option.Rel (· ≈ ·) o o := by
  cases o
  · exact Option.Rel.none
  · exact Option.Rel.some trivial
-- helper
theorem orelD (n : Nat) (o : Option Unit) : Option.Rel (fun x y => x ≡{n}≡ y) o o := by
  cases o
  · exact Option.Rel.none
  · exact Option.Rel.some OFE.Dist.rfl
-- helper
theorem delE {V : Type} : PartialMap.delete (∅ : TM V) 0 = ∅ :=
  equiv_iff_eq.mp fun k => by
    by_cases hk : 0 = k
    · rw [get?_delete_eq hk, get?_empty]
    · rw [get?_delete_ne hk]
-- helper
theorem delS {V : Type} (v : V) : PartialMap.delete (sg v) 0 = ∅ := LawfulPartialMap.delete_singleton_eq
-- helper: concrete finite sets
abbrev TS := Std.ExtTreeSet Nat compare
-- helper
theorem ssE {PROP : Type _} [BI PROP] (Φ : Nat → PROP) : bigSepS Φ ({0} : TS) ⊣⊢ Φ 0 := BigSepS.bigSepS_singleton
-- helper
theorem seE {PROP : Type _} [BI PROP] (Φ : Nat → PROP) : bigSepS Φ (∅ : TS) ⊣⊢ emp := BigSepS.bigSepS_empty
-- helper
theorem mem0 : (0 : Nat) ∈ ({0} : TS) := LawfulSet.mem_singleton.2 rfl
-- helper
theorem insS : @Insert.insert Nat TS LawfulSet.instInsert 0 {0} = {0} := LawfulSet.ext fun x => by
  rw [LawfulSet.mem_insert]
  exact ⟨fun h => h.elim (fun e => LawfulSet.mem_singleton.2 e) id, Or.inr⟩
-- helper
theorem edS : (∅ : TS) \ {0} = ∅ := LawfulSet.ext fun x => by
  rw [LawfulSet.mem_diff]; exact ⟨fun h => h.1, fun h => (LawfulSet.mem_empty h).elim⟩
-- helper
theorem s01 {PROP : Type _} [BI PROP] (Φ : Nat → PROP) : bigSepS Φ (@Insert.insert Nat TS LawfulSet.instInsert 1 {0}) ⊣⊢ iprop(Φ 1 ∗ Φ 0) :=
  (BigSepS.bigSepS_insert (by rw [LawfulSet.mem_singleton]; decide)).trans
    ⟨sep_mono_right (ssE Φ).1, sep_mono_right (ssE Φ).2⟩
/-- two-element resource algebra with equality order (not affine): o is the unit -/
-- helper: two-element resource algebra with equality order (UPred over it is non-affine; later emp is not emp)
inductive B2 | o | i deriving DecidableEq
def B2.or : B2 → B2 → B2
  | .o, y => y
  | .i, _ => .i
instance : COFE B2 := COFE.ofDiscrete _
instance : OFE.Discrete B2 := ⟨fun h => h⟩
instance : Op B2 where
  op := B2.or
  op_ne := ⟨fun _ _ _ h => by cases (h : _ = _); exact OFE.Dist.rfl⟩
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
instance : PCore B2 where
  pcore _ := some .o
  pcore_ne := by intro n x y cx _ h; cases h; exact ⟨.o, rfl, OFE.Dist.rfl⟩
  pcore_idem := by intro x cx h; cases h; rfl
instance : Valid B2 where
  ValidN _ _ := True
  Valid _ := True
  validN_ne := fun _ h => h
  valid_iff_validN := ⟨fun _ _ => trivial, fun _ => trivial⟩
  validN_succ := fun h => h
instance : Ordered B2 where
  OrderN _ x y := x = y
  Order x y := x = y
  ordN_ne := by intro n x x' y y' hx hy h; exact (hx : x = x') ▸ (hy : y = y') ▸ h
  ordN_succ := id
  ordN_trans := Eq.trans
  ord_trans := Eq.trans
  ordN_of_ord := fun _ h => h
instance : ORA B2 where
  validN_op_left := fun _ => trivial
  pcore_op_left := by intro x cx h; cases h; rfl
  extend := fun {_ _ y₁ y₂} _ h => ⟨y₁, y₂, h, OFE.Dist.rfl, OFE.Dist.rfl⟩
  op_monoN_left_ord := by intro n x y z h; exact congrArg (· • z) h
  op_mono_left_ord := by intro x y z h; exact congrArg (· • z) h
  validN_of_ordN := fun _ _ => trivial
  pcore_monoN_ord := by intro n x y cx _ h; cases h; exact ⟨.o, rfl, rfl⟩
  pcore_mono_ord := by intro x y cx _ h; cases h; exact ⟨.o, rfl, rfl⟩
  pcore_order_op := by intro x cx h y; cases h; exact ⟨.o, rfl, rfl⟩
  pcore_increasing := by intro x cx h; cases h; exact ⟨fun y => rfl⟩
  increasing_closed := by
    intro n x y hx h
    rcases h with h | h <;> (have e : x = y := h; exact e ▸ hx)
  ordN_extend := by intro n x y _ h; exact ⟨y, rfl, (h : x = y) ▸ OFE.Dist.rfl⟩
instance : OrderRefl B2 := ⟨fun _ => rfl⟩
instance : UORA B2 where
  unit := .o
  unit_valid := trivial
  unit_left_id := rfl
  pcore_unit := rfl

-- helper: in UPred B2, later emp holds at step 0 at resource i, emp does not
theorem b2_later_emp (e : (iprop(▷ emp) : UPred B2) ⊢ emp) : False := by
  have : (iprop(▷ emp) : UPred B2).holds 0 ⟨.i, trivial⟩ := by
    show (UPred.later _).holds 0 _
    trivial
  exact absurd (e 0 _ this) (fun h' => nomatch (h' : B2.o = B2.i))

-- `Iris.BI.BigSepM.bigSepM_empty_intro` idx 7: necessary (HeapProp Unit: P = True (not affine); True |- emp fails)
theorem w4c2_1 : ¬ drop0% Iris.BI.BigSepM.bigSepM_empty_intro 7 := fun h =>
  not_true_emp ((h (PROP := HeapProp Unit) (M := TM) (K := Nat) (V := Unit) (P := iprop(True))
    (Φ := fun _ _ => iprop(True))).trans BigSepM.bigSepM_empty.1)
-- `Iris.BI.BigSepM.bigSepM_eqv_of_perm` idx 9: necessary (SiProp: m1 = {0:=()}, m2 empty, Phi = False)
theorem w4c2_2 : ¬ drop0% Iris.BI.BigSepM.bigSepM_eqv_of_perm 9 := fun h => by
  have e := (h (PROP := SiProp) (M := TM) (K := Nat) (V := Unit) (Φ := fun _ _ => iprop(False))
    (m₁ := sg ()) (m₂ := ∅)).2
  rw [sgE, emE] at e
  exact sp e 0 trivial
-- `Iris.BI.BigSepM.bigSepM_eqv_empty` idx 8: necessary (SiProp: m = {0:=()}, Phi = False)
theorem w4c2_3 : ¬ drop0% Iris.BI.BigSepM.bigSepM_eqv_empty 8 := fun h => by
  have e := (h (PROP := SiProp) (M := TM) (K := Nat) (V := Unit) (Φ := fun _ _ => iprop(False))
    (m := sg ())).2
  rw [sgE] at e
  exact sp e 0 trivial
-- `Iris.BI.BigSepM.bigSepM_insert` idx 10: necessary (HeapProp Unit: m = {0:=()}, i = 0, Phi = owns cell 0; own0 * own0 = False)
theorem w4c2_4 : ¬ drop0% Iris.BI.BigSepM.bigSepM_insert 10 := fun h => by
  have e := (h (PROP := HeapProp Unit) (M := TM) (K := Nat) (V := Unit) (Φ := fun _ _ => own0)
    (m := sg ()) (i := 0) (x := ())).1
  rw [insIns, sgE] at e
  exact own0_sep_own0 (hp e h0 own0_h0)

-- `Iris.BI.BigSepM.bigSepM_delete` idx 10: necessary (SiProp: m empty, Phi = False)
theorem w4c2_5 : ¬ drop0% Iris.BI.BigSepM.bigSepM_delete 10 := fun h => by
  have e := (h (PROP := SiProp) (M := TM) (K := Nat) (V := Unit) (Φ := fun _ _ => iprop(False))
    (m := ∅) (i := 0) (x := ())).1
  rw [emE] at e
  exact sp (e.trans sep_elim_left) 0 trivial

-- `Iris.BI.BigSepM.bigSepM_mono` idx 9: necessary (SiProp: m = {0:=()}, Phi = True, Psi = False)
theorem w4c2_6 : ¬ drop0% Iris.BI.BigSepM.bigSepM_mono 9 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (V := Unit) (Φ := fun _ _ => iprop(True))
    (Ψ := fun _ _ => iprop(False)) (m := sg ())
  rw [sgE, sgE] at e
  exact sp e 0 trivial

-- `Iris.BI.BigSepM.bigSepM_eq` idx 9: necessary (SiProp: m = {0:=()}, Phi = True, Psi = False)
theorem w4c2_7 : ¬ drop0% Iris.BI.BigSepM.bigSepM_eq 9 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (V := Unit) (Φ := fun _ _ => iprop(True))
    (Ψ := fun _ _ => iprop(False)) (m := sg ())
  rw [sgE, sgE] at e
  exact hcast e trivial

-- `Iris.BI.BigSepM.bigSepM_eq_of_forall_eq` idx 9: necessary (SiProp: m = {0:=()}, Phi = True, Psi = False)
theorem w4c2_8 : ¬ drop0% Iris.BI.BigSepM.bigSepM_eq_of_forall_eq 9 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (V := Unit) (Φ := fun _ _ => iprop(True))
    (Ψ := fun _ _ => iprop(False)) (m := sg ())
  rw [sgE, sgE] at e
  exact hcast e trivial

-- `Iris.BI.BigSepM.bigSepM_dist` idx 10: necessary (SiProp, n = 0: m = {0:=()}, Phi = True, Psi = False)
theorem w4c2_9 : ¬ drop0% Iris.BI.BigSepM.bigSepM_dist 10 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (V := Unit) (Φ := fun _ _ => iprop(True))
    (Ψ := fun _ _ => iprop(False)) (m := sg ()) (n := 0)
  rw [sgE, sgE] at e
  exact (e (Nat.le_refl 0)).1 trivial

-- `Iris.BI.BigSepM.bigSepM_mono_of_forall` idx 9: necessary (SiProp: m = {0:=()}, Phi = True, Psi = False)
theorem w4c2_10 : ¬ drop0% Iris.BI.BigSepM.bigSepM_mono_of_forall 9 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (V := Unit) (Φ := fun _ _ => iprop(True))
    (Ψ := fun _ _ => iprop(False)) (m := sg ())
  rw [sgE, sgE] at e
  exact sp e 0 trivial

-- `Iris.BI.BigSepM.bigSepM_flip_mono` idx 9: necessary (SiProp: m = {0:=()}, Psi = True, Phi = False)
theorem w4c2_11 : ¬ drop0% Iris.BI.BigSepM.bigSepM_flip_mono 9 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (V := Unit) (Ψ := fun _ _ => iprop(True))
    (Φ := fun _ _ => iprop(False)) (m := sg ())
  rw [sgE, sgE] at e
  exact sp e 0 trivial

-- `Iris.BI.BigSepM.bigSepM_persistent` idx 8: necessary (HeapProp Unit: m = {0:=()}, Phi = owns cell 0, not persistent)
theorem w4c2_12 : ¬ drop0% Iris.BI.BigSepM.bigSepM_persistent 8 := fun h => by
  have e := (h (PROP := HeapProp Unit) (M := TM) (K := Nat) (V := Unit) (Φ := fun _ _ => own0)
    (m := sg ())).persistent
  rw [sgE] at e
  exact hp e h0 own0_h0 rfl

-- `Iris.BI.BigSepM.bigSepM_persistent_inst` idx 8: necessary (HeapProp Unit: m = {0:=()}, Phi = owns cell 0, not persistent)
theorem w4c2_13 : ¬ drop0% Iris.BI.BigSepM.bigSepM_persistent_inst 8 := fun h => by
  have e := (h (PROP := HeapProp Unit) (M := TM) (K := Nat) (V := Unit) (Φ := fun _ _ => own0)
    (m := sg ())).persistent
  rw [sgE] at e
  exact hp e h0 own0_h0 rfl

-- `Iris.BI.BigSepM.bigSepM_affine` idx 8: necessary (HeapProp Unit: m = {0:=()}, Phi = True, not affine)
theorem w4c2_14 : ¬ drop0% Iris.BI.BigSepM.bigSepM_affine 8 := fun h => by
  have e := (h (PROP := HeapProp Unit) (M := TM) (K := Nat) (V := Unit) (Φ := fun _ _ => iprop(True))
    (m := sg ())).affine
  rw [sgE] at e
  exact not_true_emp e

-- `Iris.BI.BigSepM.bigSepM_affine_inst` idx 8: necessary (HeapProp Unit: m = {0:=()}, Phi = True, not affine)
theorem w4c2_15 : ¬ drop0% Iris.BI.BigSepM.bigSepM_affine_inst 8 := fun h => by
  have e := (h (PROP := HeapProp Unit) (M := TM) (K := Nat) (V := Unit) (Φ := fun _ _ => iprop(True))
    (m := sg ())).affine
  rw [sgE] at e
  exact not_true_emp e

-- `Iris.BI.BigSepM.bigSepM_affine_biaffine_inst` idx 8: necessary (HeapProp Unit (not BIAffine): m = {0:=()}, Phi = True)
theorem w4c2_16 : ¬ drop0% Iris.BI.BigSepM.bigSepM_affine_biaffine_inst 8 := fun h => by
  have e := (h (PROP := HeapProp Unit) (M := TM) (K := Nat) (V := Unit) (Φ := fun _ _ => iprop(True))
    (m := sg ())).affine
  rw [sgE] at e
  exact not_true_emp e

-- `Iris.BI.BigSepM.bigSepM_timeless` idx 9: necessary (SiProp: m = {0:=()}, Phi = s0, true only at step 0)
theorem w4c2_17 : ¬ drop0% Iris.BI.BigSepM.bigSepM_timeless 9 := fun h =>
  s0_not_timeless (by rw [sgE]; exact .rfl) (h (PROP := SiProp) (M := TM) (K := Nat) (V := Unit) (Φ := fun _ _ => s0)
    (m := sg ())).timeless

-- `Iris.BI.BigSepM.bigSepM_nil_absorbing_inst` idx 6: necessary (HeapProp Unit (not BIAffine): m empty; emp not absorbing)
theorem w4c2_18 : ¬ drop0% Iris.BI.BigSepM.bigSepM_nil_absorbing_inst 6 := fun h => by
  have e := (h (PROP := HeapProp Unit) (M := TM) (K := Nat) (V := Unit) (Φ := fun _ _ => iprop(True))).absorbing
  rw [emE] at e
  exact h0_ne (hp e h0 ⟨h0, ∅, (union_comm.trans empty_union.symm).symm, fun _ => Or.inr rfl, trivial, rfl⟩)

-- `Iris.BI.BigSepM.bigSepM_absorbing` idx 9: removable (BIAffine is kept, and in an affine BI every proposition is absorbing)
theorem w4c2_19 : drop% Iris.BI.BigSepM.bigSepM_absorbing 9 := by
  intros
  exact BigSepM.bigSepM_absorbing (fun _ => inferInstance)
-- `Iris.BI.BigSepM.bigSepM_lookup_acc` idx 10: necessary (SiProp: m empty, Phi = False)
theorem w4c2_20 : ¬ drop0% Iris.BI.BigSepM.bigSepM_lookup_acc 10 := fun h => by
  have e := (h (PROP := SiProp) (M := TM) (K := Nat) (V := Unit) (Φ := fun _ _ => iprop(False))
    (m := ∅) (i := 0) (x := ())).1
  rw [emE] at e
  exact sp (e.trans sep_elim_left) 0 trivial

-- `Iris.BI.BigSepM.bigSepM_lookup` idx 10: necessary (SiProp: m empty, Phi = False)
theorem w4c2_21 : ¬ drop0% Iris.BI.BigSepM.bigSepM_lookup 10 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (V := Unit) (Φ := fun _ _ => iprop(False))
    (m := ∅) (i := 0) (x := ())
  rw [emE] at e
  exact sp e 0 trivial

-- `Iris.BI.BigSepM.bigSepM_lookup_dom` idx 10: necessary (SiProp: m empty, Phi = False)
theorem w4c2_22 : ¬ drop0% Iris.BI.BigSepM.bigSepM_lookup_dom 10 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (V := Unit) (Φ := fun _ => iprop(False))
    (m := ∅) (i := 0) (x := ())
  rw [emE] at e
  exact sp e 0 trivial

-- `Iris.BI.BigSepM.bigSepM_insert_acc` idx 10: necessary (SiProp: m empty, Phi = False)
theorem w4c2_23 : ¬ drop0% Iris.BI.BigSepM.bigSepM_insert_acc 10 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (V := Unit) (Φ := fun _ _ => iprop(False))
    (m := ∅) (i := 0) (x := ())
  rw [emE] at e
  exact sp (e.trans sep_elim_left) 0 trivial

-- `Iris.BI.BigSepM.bigSepM_lookup_acc_impl` idx 11: necessary (SiProp: m empty, Phi = False)
theorem w4c2_24 : ¬ drop0% Iris.BI.BigSepM.bigSepM_lookup_acc_impl 11 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (V := Unit) (Φ := fun _ _ => iprop(False))
    (m := ∅) (i := 0) (x := ())
  rw [emE] at e
  exact sp (e.trans sep_elim_left) 0 trivial

-- `Iris.BI.BigSepM.bigSepM_insert_exist` idx 11: necessary (SiProp: m empty, i = 0, Phi = False: the singleton map is not empty)
theorem w4c2_25 : ¬ drop0% Iris.BI.BigSepM.bigSepM_insert_exist 11 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (V := Unit) (Φ := fun _ _ => iprop(False))
    (m := ∅) (i := 0) (x := ()) (x' := ()) rfl
  rw [emE] at e
  exact hcast (P := iprop(emp)) (Q := iprop(False)) (e.symm.trans (sgE _ ())) trivial

-- `Iris.BI.BigSepM.bigSepM_insert_exist` idx 12: necessary (SiProp: m = {0:=false}, x' = true, Phi b = (b = true))
theorem w4c2_26 : ¬ drop0% Iris.BI.BigSepM.bigSepM_insert_exist 12 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (V := Bool) (Φ := fun _ b => iprop(⌜b = true⌝))
    (m := sg false) (i := 0) (x := false) (x' := true) (sg_get false)
  rw [insIns, sgE, sgE] at e
  exact Bool.false_ne_true (hcast e rfl)

-- `Iris.BI.BigSepM.bigSepM_insert_exist_elim` idx 11: necessary (SiProp: m empty, i = 0, Phi = False)
theorem w4c2_27 : ¬ drop0% Iris.BI.BigSepM.bigSepM_insert_exist_elim 11 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (V := Unit) (Φ := fun _ _ => iprop(False))
    (m := ∅) (i := 0) (x := ()) (x' := ()) .rfl
  rw [emE] at e
  exact sp (e.trans (BiEntails.of_eq (sgE _ ())).1) 0 trivial

-- `Iris.BI.BigSepM.bigSepM_insert_exist_elim` idx 12: necessary (SiProp: m = {0:=false}, x' = true, Phi b = (b = false))
theorem w4c2_28 : ¬ drop0% Iris.BI.BigSepM.bigSepM_insert_exist_elim 12 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (V := Bool) (Φ := fun _ b => iprop(⌜b = false⌝))
    (m := sg false) (i := 0) (x := false) (x' := true) (sg_get false)
  rw [insIns, sgE, sgE] at e
  exact Bool.false_ne_true (sp e 0 rfl).symm

-- `Iris.BI.BigSepM.bigSepM_insert_exist_intro` idx 11: necessary (HeapProp Unit: m empty, i = 0, Phi = True; True |- emp fails)
theorem w4c2_29 : ¬ drop0% Iris.BI.BigSepM.bigSepM_insert_exist_intro 11 := fun h => by
  have e := h (PROP := HeapProp Unit) (M := TM) (K := Nat) (V := Unit) (Φ := fun _ _ => iprop(True))
    (m := ∅) (i := 0) (x := ()) (x' := ()) .rfl
  rw [emE] at e
  exact not_true_emp ((BiEntails.of_eq (sgE (fun _ _ => (iprop(True) : HeapProp Unit)) ())).2.trans e)

-- `Iris.BI.BigSepM.bigSepM_insert_exist_intro` idx 12: necessary (SiProp: m = {0:=false}, x' = true, Phi b = (b = true))
theorem w4c2_30 : ¬ drop0% Iris.BI.BigSepM.bigSepM_insert_exist_intro 12 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (V := Bool) (Φ := fun _ b => iprop(⌜b = true⌝))
    (m := sg false) (i := 0) (x := false) (x' := true) (sg_get false)
  rw [insIns, sgE, sgE] at e
  exact Bool.false_ne_true (sp e 0 rfl)

-- `Iris.BI.BigSepM.bigSepM_fn_insert` idx 14: necessary (SiProp: m = {0:=()}, i = 0, B = Bool, b = true, f = false, g k y c = (c = true))
theorem w4c2_31 : ¬ drop0% Iris.BI.BigSepM.bigSepM_fn_insert 14 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (V := Unit) (B := Bool) (g := fun _ _ c => iprop(⌜c = true⌝))
    (f := fun _ => false) (m := sg ()) (i := 0) (x := ()) (b := true)
  rw [insIns, sgE, sgE] at e
  exact Bool.false_ne_true (hcast e rfl).2

-- `Iris.BI.BigSepM.bigSepM_fn_insert_key` idx 12: necessary (SiProp: m = {0:=()}, i = 0, P = True, f = False)
theorem w4c2_32 : ¬ drop0% Iris.BI.BigSepM.bigSepM_fn_insert_key 12 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (V := Unit) (f := fun _ => iprop(False))
    (m := sg ()) (i := 0) (x := ()) (P := iprop(True))
  rw [insIns, sgE, sgE] at e
  exact (hcast e trivial).2

-- `Iris.BI.BigSepM.bigSepM_intro` idx 7: necessary (HeapProp Unit: m empty, P = True (not intuitionistic); True |- emp fails)
theorem w4c2_33 : ¬ drop0% Iris.BI.BigSepM.bigSepM_intro 7 := fun h => by
  have e := h (PROP := HeapProp Unit) (M := TM) (K := Nat) (V := Unit) (P := iprop(True))
    (Φ := fun _ _ => iprop(True)) (m := ∅) (fun _ => .rfl)
  rw [emE] at e
  exact not_true_emp e

-- `Iris.BI.BigSepM.bigSepM_intro` idx 10: necessary (SiProp: m = {0:=()}, P = emp, Phi = False)
theorem w4c2_34 : ¬ drop0% Iris.BI.BigSepM.bigSepM_intro 10 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (V := Unit) (P := iprop(emp))
    (Φ := fun _ _ => iprop(False)) (m := sg ())
  rw [sgE] at e
  exact sp e 0 trivial

-- `Iris.BI.BigSepM.bigSepM_forall_intro` idx 9: removable (BIAffine is kept: each conjunct is extracted by bigSepM_lookup, whose Affine side condition BIAffine provides)
theorem w4c2_35 : drop% Iris.BI.BigSepM.bigSepM_forall_intro 9 := by
  intros
  exact forall_intro fun _ => forall_intro fun _ => imp_intro_swap <|
    pure_elim_left fun hget => BigSepM.bigSepM_lookup hget

-- `Iris.BI.BigSepM.bigSepM_forall_elim` idx 8: necessary (HeapProp Unit (not BIAffine): m empty, Phi = True; True |- emp fails)
theorem w4c2_36 : ¬ drop0% Iris.BI.BigSepM.bigSepM_forall_elim 8 := fun h => by
  have e := h (PROP := HeapProp Unit) (M := TM) (K := Nat) (V := Unit)
    (Φ := fun _ _ => iprop(True)) (m := ∅) (inst := fun _ _ => pure_persistent True)
  rw [emE] at e
  exact not_true_emp ((forall_intro fun _ => forall_intro fun _ => imp_intro and_elim_l).trans e)

-- `Iris.BI.BigSepM.bigSepM_forall` idx 8: necessary (HeapProp Unit (not BIAffine): m empty, Phi = True; True |- emp fails)
theorem w4c2_37 : ¬ drop0% Iris.BI.BigSepM.bigSepM_forall 8 := fun h => by
  have e := (@h (HeapProp Unit) _ Nat Unit TM _ (fun _ _ => iprop(True)) ∅ (fun _ _ => pure_persistent True)).2
  rw [emE] at e
  exact not_true_emp ((forall_intro fun _ => forall_intro fun _ => imp_intro and_elim_l).trans e)

-- `Iris.BI.BigSepM.bigSepM_dup` idx 7: necessary (HeapProp Unit: P = True (not affine), m empty)
theorem w4c2_38 : ¬ drop0% Iris.BI.BigSepM.bigSepM_dup 7 := fun h => by
  have e := h (PROP := HeapProp Unit) (M := TM) (K := Nat) (V := Unit) (P := iprop(True)) (m := ∅)
  rw [emE] at e
  exact h0_ne (hp e h0 ⟨∅, h0, empty_union, empty_disjoint,
    ⟨rfl, fun σ' _ _ => ⟨∅, ∅ ∪ σ', empty_union, empty_disjoint, trivial, trivial⟩⟩, trivial⟩)

-- `Iris.BI.BigSepM.bigSepM_persistently` idx 8: necessary (HeapProp Unit (not BIAffine): m empty; pers emp holds everywhere, emp does not)
theorem w4c2_39 : ¬ drop0% Iris.BI.BigSepM.bigSepM_persistently 8 := fun h => by
  have e := (h (PROP := HeapProp Unit) (M := TM) (K := Nat) (V := Unit) (Φ := fun _ _ => iprop(True)) (m := ∅)).1
  rw [emE, emE] at e
  exact h0_ne (hp e h0 rfl)

-- `Iris.BI.BigSepM.bigSepM_union` idx 10: necessary (HeapProp Unit: m1 = m2 = {0:=()}, Phi = owns cell 0)
theorem w4c2_40 : ¬ drop0% Iris.BI.BigSepM.bigSepM_union 10 := fun h => by
  have e := (h (PROP := HeapProp Unit) (M := TM) (K := Nat) (V := Unit) (Φ := fun _ _ => own0)
    (m₁ := sg ()) (m₂ := sg ())).1
  rw [unionSelf, sgE] at e
  exact own0_sep_own0 (hp e h0 own0_h0)

-- `Iris.BI.BigSepM.bigSepM_subseteq` idx 10: necessary (HeapProp Unit: m1 = {0:=()}, m2 empty, Phi = True (not affine))
theorem w4c2_41 : ¬ drop0% Iris.BI.BigSepM.bigSepM_subseteq 10 := fun h => by
  have e := h (PROP := HeapProp Unit) (M := TM) (K := Nat) (V := Unit) (Φ := fun _ _ => iprop(True))
    (m₁ := sg ()) (m₂ := ∅) (fun k v hk => by rw [get?_empty] at hk; cases hk)
  rw [sgE, emE] at e
  exact not_true_emp e

-- `Iris.BI.BigSepM.bigSepM_sep_zipWith` idx 16: necessary (SiProp: m1 = {0:=()}, m2 = {0:=false}, f = const (), g2 = const true, Phi2 b = (b = true))
theorem w4c2_42 : ¬ drop0% Iris.BI.BigSepM.bigSepM_sep_zipWith 16 := fun h => by
  have e := (h (PROP := SiProp) (M := TM) (K := Nat) (A := Unit) (B := Bool) (C := Unit) (f := fun _ _ => ())
    (g₁ := fun _ => ()) (g₂ := fun _ => true) (Φ₁ := fun _ _ => iprop(True)) (Φ₂ := fun _ b => iprop(⌜b = true⌝))
    (m₁ := sg ()) (m₂ := sg false) rfl (domSg () false)).1
  rw [zw, sgE, sgE, sgE] at e
  exact Bool.false_ne_true (sp e 0 ⟨trivial, rfl⟩).2

-- `Iris.BI.BigSepM.bigSepM_sep_zipWith` idx 17: necessary (SiProp: m1 = {0:=()}, m2 empty, f = pairing, Phi1 = False)
theorem w4c2_43 : ¬ drop0% Iris.BI.BigSepM.bigSepM_sep_zipWith 17 := fun h => by
  have e := (h (PROP := SiProp) (M := TM) (K := Nat) (A := Unit) (B := Unit) (C := Unit × Unit) (f := Prod.mk)
    (g₁ := Prod.fst) (g₂ := Prod.snd) (Φ₁ := fun _ _ => iprop(False)) (Φ₂ := fun _ _ => iprop(True))
    (m₁ := sg ()) (m₂ := ∅) rfl rfl).1
  rw [zwE, emE, sgE] at e
  exact sp (e.trans sep_elim_left) 0 trivial

-- `Iris.BI.BigSepM.bigSepM_sep_zip` idx 11: necessary (SiProp: m1 = {0:=()}, m2 empty, Phi1 = False)
theorem w4c2_44 : ¬ drop0% Iris.BI.BigSepM.bigSepM_sep_zip 11 := fun h => by
  have e := (h (PROP := SiProp) (M := TM) (K := Nat) (A := Unit) (B := Unit)
    (Φ₁ := fun _ _ => iprop(False)) (Φ₂ := fun _ _ => iprop(True)) (m₁ := sg ()) (m₂ := ∅)).1
  rw [PartialMap.zip, zwE, emE, sgE] at e
  exact sp (e.trans sep_elim_left) 0 trivial
-- `Iris.BI.BigSepM.bigSepM_pure` idx 6: necessary (HeapProp Unit (not BIAffine): m empty, phi = True; emp is not the pure True)
theorem w4c2_45 : ¬ drop0% Iris.BI.BigSepM.bigSepM_pure 6 := fun h => by
  have e := (h (PROP := HeapProp Unit) (M := TM) (K := Nat) (V := Unit) (φ := fun _ _ => True) (m := ∅)).2
  rw [emE] at e
  exact h0_ne (hp e h0 (fun _ _ _ => trivial))

-- `Iris.BI.BigSepM.bigSepM_filter` idx 6: necessary (HeapProp Unit (not BIAffine): m = {0:=()}, p = false, Phi = True; emp vs (False -> True))
theorem w4c2_46 : ¬ drop0% Iris.BI.BigSepM.bigSepM_filter 6 := fun h => by
  have e := h (PROP := HeapProp Unit) (M := TM) (K := Nat) (V := Unit) (Φ := fun _ _ => iprop(True))
    (m := sg ()) (fun _ _ => false)
  rw [BigSepM.bigSepM_filter_cond, sgE, sgE] at e
  have : (iprop(emp) : HeapProp Unit) h0 := by
    have e' := congrFun e h0
    simp only [Bool.false_eq_true, ↓reduceIte] at e'
    exact e'.mpr (fun hf => False.elim hf)
  exact h0_ne this

-- `Iris.BI.BigSepM.bigSepM_ofList` idx 9: necessary (HeapProp Unit: l = [(0,()),(0,())], Phi = owns cell 0)
theorem w4c2_47 : ¬ drop0% Iris.BI.BigSepM.bigSepM_ofList 9 := fun h => by
  have e := (h (PROP := HeapProp Unit) (M := TM) (K := Nat) (V := Unit) (Φ := fun _ _ => own0)
    (l := [(0, ()), (0, ())])).1
  rw [ofListU _ (by simp) (by simp), sgE] at e
  exact own0_sep_own0 (hp (e.trans (BigSepL.bigSepL_cons.1.trans (sep_mono_right BigSepL.bigSepL_singleton.1))) h0 own0_h0)

-- `Iris.BI.BigSepM.bigSepM_kmap` idx 13: necessary (HeapProp Unit: f = const 0, m = {0:=(),1:=()}, Phi = owns cell 0)
theorem w4c2_48 : ¬ drop0% Iris.BI.BigSepM.bigSepM_kmap 13 := fun h => by
  have e := (h (PROP := HeapProp Unit) (M := TM) (K := Nat) (V := Unit) (M' := TM) (K' := Nat)
    (f := fun _ => 0) (Φ := fun _ _ => own0) (m := tw () ())).1
  have hk : (FiniteMap.kmap (fun _ => 0) (tw () ()) : TM Unit) = sg () := by
    refine ofListU _ (fun e he => ?_) (fun hnil => ?_)
    · obtain ⟨kv, _, rfl⟩ := List.mem_map.mp he; rfl
    · have hm : ((1 : Nat), ()) ∈ toList (tw () ()) := (toList_get (M := TM) (K := Nat)).mpr (get?_insert_eq rfl)
      rw [List.map_eq_nil_iff] at hnil; rw [hnil] at hm; cases hm
  rw [hk, sgE, twE] at e
  exact own0_sep_own0 (hp e h0 own0_h0)

-- `Iris.BI.BigSepM.bigSepM_impl_dom_subseteq` idx 16: necessary (SiProp: m1 empty (V = Empty), m2 = {0:=()}, Psi = False)
theorem w4c2_49 : ¬ drop0% Iris.BI.BigSepM.bigSepM_impl_dom_subseteq 16 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (V := Empty) (M₂ := TM) (V₂ := Unit)
    (S := Std.ExtTreeSet Nat compare) (Φ := fun _ _ => iprop(True)) (Ψ := fun _ _ => iprop(False))
    (m₁ := ∅) (m₂ := sg ())
  rw [emE, sgE] at e
  refine sp (((emp_sep (P := iprop(emp))).2.trans (sep_mono e ?_)).trans (wand_elim_left.trans sep_elim_left)) 0 trivial
  exact intuitionistically_emp.2.trans (intuitionistically_mono (forall_intro fun _ => forall_intro fun x => x.elim))

-- `Iris.BI.BigSepM2.bigSepM2_empty_intro` idx 8: necessary (HeapProp Unit: P = True (not affine))
theorem w4c2_50 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_empty_intro 8 := fun h =>
  not_true_emp ((h (PROP := HeapProp Unit) (M := TM) (K := Nat) (A := Unit) (B := Unit) iprop(True)
    (fun _ _ _ => iprop(True))).trans (BigSepM2.bigSepM2_empty _).1)

-- `Iris.BI.BigSepM2.bigSepM2_delete` idx 13: necessary (SiProp: m1 = {0:=false}, x1 = true, m2 = {0:=()}, Phi a b = (a = false))
theorem w4c2_51 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_delete 13 := fun h => by
  have e := (h (PROP := SiProp) (M := TM) (K := Nat) (A := Bool) (B := Unit) (Φ := fun _ a _ => iprop(⌜a = false⌝))
    (m1 := sg false) (m2 := sg ()) (i := 0) (x1 := true) (x2 := ()) (sg_get ())).1
  exact Bool.false_ne_true ((sp ((s2E _ _ _).2.trans (e.trans sep_elim_left)) 0 rfl)).symm

-- `Iris.BI.BigSepM2.bigSepM2_insert` idx 13: necessary (SiProp: m1 = {0:=()}, m2 empty, i = 0, Phi = True)
theorem w4c2_52 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_insert 13 := fun h => by
  have e := (h (PROP := SiProp) (M := TM) (K := Nat) (A := Unit) (B := Unit) (Φ := fun _ _ _ => iprop(True))
    (m1 := sg ()) (m2 := ∅) (i := 0) (x1 := ()) (x2 := ()) (get?_empty 0)).1
  rw [insIns] at e
  exact sg_ne () (sp (((s2E _ _ _).2.trans e).trans (sep_elim_right.trans (BigSepM2.bigSepM2_empty_left _ _))) 0 trivial)

-- `Iris.BI.BigSepM2.bigSepM2_insert` idx 14: necessary (SiProp: m1 empty, m2 = {0:=()}, i = 0, Phi = True)
theorem w4c2_53 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_insert 14 := fun h => by
  have e := (h (PROP := SiProp) (M := TM) (K := Nat) (A := Unit) (B := Unit) (Φ := fun _ _ _ => iprop(True))
    (m1 := ∅) (m2 := sg ()) (i := 0) (x1 := ()) (x2 := ()) (get?_empty 0)).1
  rw [insIns] at e
  exact sg_ne () (sp (((s2E _ _ _).2.trans e).trans (sep_elim_right.trans (BigSepM2.bigSepM2_empty_right _ _))) 0 trivial)

-- `Iris.BI.BigSepM2.bigSepM2_mono` idx 11: necessary (SiProp: m1 = m2 = {0:=()}, Phi = True, Psi = False)
theorem w4c2_54 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_mono 11 := fun h =>
  sp (((s2E _ _ _).2.trans (h (PROP := SiProp) (M := TM) (K := Nat) (A := Unit) (B := Unit)
    (Φ := fun _ _ _ => iprop(True)) (Ψ := fun _ _ _ => iprop(False)) (m1 := sg ()) (m2 := sg ()))).trans (s2E _ _ _).1) 0 trivial

-- `Iris.BI.BigSepM2.bigSepM2_dist` idx 12: necessary (SiProp, n = 0: m1 = m2 = {0:=()}, Phi = True, Psi = False)
theorem w4c2_55 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_dist 12 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (A := Unit) (B := Unit)
    (fun _ _ _ => iprop(True)) (fun _ _ _ => iprop(False)) (sg ()) (sg ()) 0
  exact sp (s2E _ _ _).1 0 ((e (Nat.le_refl 0)).1 (sp (s2E _ _ _).2 0 trivial))

-- `Iris.BI.BigSepM2.bigSepM2_eqv` idx 11: necessary (SiProp: m1 = m2 = {0:=()}, Phi = True, Psi = False)
theorem w4c2_56 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_eqv 11 := fun h =>
  sp (((s2E _ _ _).2.trans (h (PROP := SiProp) (M := TM) (K := Nat) (A := Unit) (B := Unit)
    (Φ := fun _ _ _ => iprop(True)) (Ψ := fun _ _ _ => iprop(False)) (m1 := sg ()) (m2 := sg ())).1).trans (s2E _ _ _).1) 0 trivial

-- `Iris.BI.BigSepM2.bigSepM2_dist_of_forall` idx 12: necessary (SiProp, n = 0: m1 = m2 = {0:=()}, Phi = True, Psi = False)
theorem w4c2_57 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_dist_of_forall 12 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (A := Unit) (B := Unit) 0
    (fun _ _ _ => iprop(True)) (fun _ _ _ => iprop(False)) (sg ()) (sg ())
  exact sp (s2E _ _ _).1 0 ((e (Nat.le_refl 0)).1 (sp (s2E _ _ _).2 0 trivial))

-- `Iris.BI.BigSepM2.bigSepM2_mono_of_forall` idx 11: necessary (SiProp: m1 = m2 = {0:=()}, Phi = True, Psi = False)
theorem w4c2_58 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_mono_of_forall 11 := fun h =>
  sp (((s2E _ _ _).2.trans (h (PROP := SiProp) (M := TM) (K := Nat) (A := Unit) (B := Unit)
    (fun _ _ _ => iprop(True)) (fun _ _ _ => iprop(False)) (sg ()) (sg ()))).trans (s2E _ _ _).1) 0 trivial

-- `Iris.BI.BigSepM2.bigSepM2_flip_mono` idx 11: necessary (SiProp: m1 = m2 = {0:=()}, Psi = True, Phi = False)
theorem w4c2_59 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_flip_mono 11 := fun h =>
  sp (((s2E _ _ _).2.trans (h (PROP := SiProp) (M := TM) (K := Nat) (A := Unit) (B := Unit)
    (fun _ _ _ => iprop(False)) (fun _ _ _ => iprop(True)) (sg ()) (sg ()))).trans (s2E _ _ _).1) 0 trivial

-- `Iris.BI.BigSepM2.bigSepM2_eqv_of_forall` idx 11: necessary (SiProp: m1 = m2 = {0:=()}, Phi = True, Psi = False)
theorem w4c2_60 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_eqv_of_forall 11 := fun h =>
  sp (((s2E _ _ _).2.trans (h (PROP := SiProp) (M := TM) (K := Nat) (A := Unit) (B := Unit)
    (fun _ _ _ => iprop(True)) (fun _ _ _ => iprop(False)) (sg ()) (sg ())).1).trans (s2E _ _ _).1) 0 trivial
-- `Iris.BI.BigSepM2.bigSepM2_proper_2` idx 15: necessary (SiProp: m1 = {0:=()}, m1' empty, m2 = m2' = {0:=()}, Phi = Psi = True)
theorem w4c2_61 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_proper_2 15 := fun h => by
  have e := (h (PROP := SiProp) (M := TM) (K := Nat) (A := Unit) (B := Unit) (fun _ _ _ => iprop(True))
    (fun _ _ _ => iprop(True)) (sg ()) (sg ()) ∅ (sg ()) (fun _ => orelU _)
    (fun _ h1' => by rw [get?_empty] at h1'; cases h1')).1
  exact sg_ne () (sp (((s2E _ _ _).2.trans e).trans (BigSepM2.bigSepM2_empty_right _ _)) 0 trivial)

-- `Iris.BI.BigSepM2.bigSepM2_proper_2` idx 16: necessary (SiProp: m1 = m1' = m2 = {0:=()}, m2' empty, Phi = Psi = True)
theorem w4c2_62 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_proper_2 16 := fun h => by
  have e := (h (PROP := SiProp) (M := TM) (K := Nat) (A := Unit) (B := Unit) (fun _ _ _ => iprop(True))
    (fun _ _ _ => iprop(True)) (sg ()) (sg ()) (sg ()) ∅ (fun _ => orelU _)
    (fun _ _ _ _ h2' => by rw [get?_empty] at h2'; cases h2')).1
  exact sg_ne () (sp (((s2E _ _ _).2.trans e).trans (BigSepM2.bigSepM2_empty_left _ _)) 0 trivial)

-- `Iris.BI.BigSepM2.bigSepM2_proper_2` idx 17: necessary (SiProp: all four maps {0:=()}, Phi = True, Psi = False)
theorem w4c2_63 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_proper_2 17 := fun h => by
  have e := (h (PROP := SiProp) (M := TM) (K := Nat) (A := Unit) (B := Unit) (fun _ _ _ => iprop(True))
    (fun _ _ _ => iprop(False)) (sg ()) (sg ()) (sg ()) (sg ()) (fun _ => orelU _) (fun _ => orelU _)).1
  exact sp (((s2E _ _ _).2.trans e).trans (s2E _ _ _).1) 0 trivial

-- `Iris.BI.BigSepM2.bigSepM2_closed` idx 12: necessary (SiProp: P Q = (Q |- False), maps empty; emp is not refutable)
theorem w4c2_64 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_closed 12 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (A := Unit) (B := Unit) (fun Q => Q ⊢ iprop(False))
    (fun _ _ _ => iprop(True)) ∅ ∅ (fun e => ⟨fun h => e.2.trans h, fun h => e.1.trans h⟩) .rfl
    (fun _ _ h1 _ => sep_elim_left.trans h1) (fun h1 _ => by rw [get?_empty] at h1; cases h1)
  exact sp ((BigSepM2.bigSepM2_empty _).2.trans e) 0 trivial

-- `Iris.BI.BigSepM2.bigSepM2_closed` idx 13: necessary (SiProp: P Q = (emp |- Q), m1 = {0:=()}, m2 empty)
theorem w4c2_65 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_closed 13 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (A := Unit) (B := Unit) (fun Q => iprop(emp) ⊢ Q)
    (fun _ _ _ => iprop(True)) (sg ()) ∅ (fun e => ⟨fun h => h.trans e.1, fun h => h.trans e.2⟩) .rfl
    (fun _ _ h1 h2 => (emp_sep (P := iprop(emp))).2.trans (sep_mono h1 h2))
    (fun _ h2 => by rw [get?_empty] at h2; cases h2)
  exact sg_ne () (sp (e.trans (BigSepM2.bigSepM2_empty_left _ _)) 0 trivial)

-- `Iris.BI.BigSepM2.bigSepM2_closed` idx 15: necessary (HeapProp Unit: P Q = (Q |- emp), m1 = m2 = {0:=()}, Phi = True)
theorem w4c2_66 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_closed 15 := fun h => by
  have e := h (PROP := HeapProp Unit) (M := TM) (K := Nat) (A := Unit) (B := Unit) (fun Q => Q ⊢ iprop(emp))
    (fun _ _ _ => iprop(True)) (sg ()) (sg ()) (fun e => ⟨fun h => e.2.trans h, fun h => e.1.trans h⟩) .rfl
    false_elim (fun _ _ h1 h2 => (sep_mono h1 h2).trans sep_emp.1)
  exact not_true_emp ((s2E _ _ _).2.trans e)

-- `Iris.BI.BigSepM2.bigSepM2_persistent` idx 10: necessary (HeapProp Unit: m1 = m2 = {0:=()}, Phi = owns cell 0)
theorem w4c2_67 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_persistent 10 := fun h =>
  hp ((s2E _ _ _).2.trans ((h (PROP := HeapProp Unit) (M := TM) (K := Nat) (A := Unit) (B := Unit)
    (fun _ _ _ => own0) (sg ()) (sg ())).persistent.trans (persistently_mono (s2E _ _ _).1))) h0 own0_h0 rfl

-- `Iris.BI.BigSepM2.bigSepM2_persistent_inst` idx 10: necessary (HeapProp Unit: m1 = m2 = {0:=()}, Phi = owns cell 0)
theorem w4c2_68 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_persistent_inst 10 := fun h =>
  hp ((s2E _ _ _).2.trans ((h (PROP := HeapProp Unit) (M := TM) (K := Nat) (A := Unit) (B := Unit)
    (Φ := fun _ _ _ => own0) (m1 := sg ()) (m2 := sg ())).persistent.trans (persistently_mono (s2E _ _ _).1))) h0 own0_h0 rfl

-- `Iris.BI.BigSepM2.bigSepM2_affine` idx 10: necessary (HeapProp Unit: m1 = m2 = {0:=()}, Phi = True)
theorem w4c2_69 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_affine 10 := fun h =>
  not_true_emp ((s2E _ _ _).2.trans (h (PROP := HeapProp Unit) (M := TM) (K := Nat) (A := Unit) (B := Unit)
    (fun _ _ _ => iprop(True)) (sg ()) (sg ())).affine)

-- `Iris.BI.BigSepM2.bigSepM2_affine_inst` idx 10: necessary (HeapProp Unit: m1 = m2 = {0:=()}, Phi = True)
theorem w4c2_70 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_affine_inst 10 := fun h =>
  not_true_emp ((s2E _ _ _).2.trans (h (PROP := HeapProp Unit) (M := TM) (K := Nat) (A := Unit) (B := Unit)
    (Φ := fun _ _ _ => iprop(True)) (m1 := sg ()) (m2 := sg ())).affine)

-- `Iris.BI.BigSepM2.bigSepM2_timeless` idx 11: necessary (SiProp: m1 = m2 = {0:=()}, Phi = s0, true only at step 0)
theorem w4c2_71 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_timeless 11 := fun h =>
  s0_not_timeless (s2E _ _ _) (h (PROP := SiProp) (M := TM) (K := Nat) (A := Unit) (B := Unit)
    (fun _ _ _ => s0) (sg ()) (sg ())).timeless

-- `Iris.BI.BigSepM2.bigSepM2_timeless_inst` idx 11: necessary (SiProp: m1 = m2 = {0:=()}, Phi = s0, true only at step 0)
theorem w4c2_72 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_timeless_inst 11 := fun h =>
  s0_not_timeless (s2E _ _ _) (h (PROP := SiProp) (M := TM) (K := Nat) (A := Unit) (B := Unit)
    (Φ := fun _ _ _ => s0) (m1 := sg ()) (m2 := sg ())).timeless

-- `Iris.BI.BigSepM2.bigSepM2_delete_left` idx 12: necessary (SiProp: m1 = {0:=false}, x1 = true, m2 = {0:=()}, Phi a b = (a = false))
theorem w4c2_73 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_delete_left 12 := fun h => by
  have e := (h (PROP := SiProp) (M := TM) (K := Nat) (A := Bool) (B := Unit) (Φ := fun _ a _ => iprop(⌜a = false⌝))
    (m1 := sg false) (m2 := sg ()) (i := 0) (x1 := true)).1
  exact Bool.false_ne_true (sp ((s2E _ _ _).2.trans (e.trans (exists_elim fun _ => and_elim_r.trans sep_elim_left))) 0 rfl).symm

-- `Iris.BI.BigSepM2.bigSepM2_insert_acc` idx 13: necessary (SiProp: m1 = {0:=false}, x1 = true, m2 = {0:=()}, Phi a b = (a = false))
theorem w4c2_74 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_insert_acc 13 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (A := Bool) (B := Unit) (Φ := fun _ a _ => iprop(⌜a = false⌝))
    (m1 := sg false) (m2 := sg ()) (i := 0) (x1 := true) (x2 := ()) (sg_get ())
  exact Bool.false_ne_true (sp ((s2E _ _ _).2.trans (e.trans sep_elim_left)) 0 rfl).symm

-- `Iris.BI.BigSepM2.bigSepM2_insert_acc` idx 14: necessary (SiProp: m1 = {0:=()}, m2 = {0:=false}, x2 = true, Phi a b = (b = false))
theorem w4c2_75 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_insert_acc 14 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (A := Unit) (B := Bool) (Φ := fun _ _ b => iprop(⌜b = false⌝))
    (m1 := sg ()) (m2 := sg false) (i := 0) (x1 := ()) (x2 := true) (sg_get ())
  exact Bool.false_ne_true (sp ((s2E _ _ _).2.trans (e.trans sep_elim_left)) 0 rfl).symm

-- `Iris.BI.BigSepM2.bigSepM2_lookup_acc` idx 13: necessary (SiProp: m1 = {0:=false}, x1 = true, m2 = {0:=()}, Phi a b = (a = false))
theorem w4c2_76 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_lookup_acc 13 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (A := Bool) (B := Unit) (Φ := fun _ a _ => iprop(⌜a = false⌝))
    (m1 := sg false) (m2 := sg ()) (i := 0) (x1 := true) (x2 := ()) (sg_get ())
  exact Bool.false_ne_true (sp ((s2E _ _ _).2.trans (e.trans sep_elim_left)) 0 rfl).symm

-- `Iris.BI.BigSepM2.bigSepM2_lookup_acc` idx 14: necessary (SiProp: m1 = {0:=()}, m2 = {0:=false}, x2 = true, Phi a b = (b = false))
theorem w4c2_77 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_lookup_acc 14 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (A := Unit) (B := Bool) (Φ := fun _ _ b => iprop(⌜b = false⌝))
    (m1 := sg ()) (m2 := sg false) (i := 0) (x1 := ()) (x2 := true) (sg_get ())
  exact Bool.false_ne_true (sp ((s2E _ _ _).2.trans (e.trans sep_elim_left)) 0 rfl).symm

-- `Iris.BI.BigSepM2.bigSepM2_lookup` idx 14: necessary (SiProp: m1 = {0:=false}, x1 = true, m2 = {0:=()}, Phi a b = (a = false))
theorem w4c2_78 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_lookup 14 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (A := Bool) (B := Unit) (Φ := fun _ a _ => iprop(⌜a = false⌝))
    (m1 := sg false) (m2 := sg ()) (i := 0) (x1 := true) (x2 := ()) (sg_get ())
  exact Bool.false_ne_true (sp ((s2E _ _ _).2.trans e) 0 rfl).symm

-- `Iris.BI.BigSepM2.bigSepM2_lookup` idx 15: necessary (SiProp: m1 = {0:=()}, m2 = {0:=false}, x2 = true, Phi a b = (b = false))
theorem w4c2_79 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_lookup 15 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (A := Unit) (B := Bool) (Φ := fun _ _ b => iprop(⌜b = false⌝))
    (m1 := sg ()) (m2 := sg false) (i := 0) (x1 := ()) (x2 := true) (sg_get ())
  exact Bool.false_ne_true (sp ((s2E _ _ _).2.trans e) 0 rfl).symm

-- `Iris.BI.BigSepM2.bigSepM2_lookup_left` idx 13: necessary (SiProp: m1 = {0:=false}, x1 = true, m2 = {0:=()}, Phi a b = (a = false))
theorem w4c2_80 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_lookup_left 13 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (A := Bool) (B := Unit) (Φ := fun _ a _ => iprop(⌜a = false⌝))
    (m1 := sg false) (m2 := sg ()) (i := 0) (x1 := true)
  exact Bool.false_ne_true (sp ((s2E _ _ _).2.trans (e.trans (exists_elim fun _ => and_elim_r))) 0 rfl).symm

-- `Iris.BI.BigSepM2.bigSepM2_lookup_right` idx 13: necessary (SiProp: m1 = {0:=()}, m2 = {0:=false}, x2 = true, Phi a b = (b = false))
theorem w4c2_81 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_lookup_right 13 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (A := Unit) (B := Bool) (fun _ _ b => iprop(⌜b = false⌝))
    (sg ()) (sg false) 0 true
  exact Bool.false_ne_true (sp ((s2E _ _ _).2.trans (e.trans (exists_elim fun _ => and_elim_r))) 0 rfl).symm

-- `Iris.BI.BigSepM2.bigSepM2_lookup_acc_impl` idx 14: necessary (SiProp: m1 = {0:=false}, x1 = true, m2 = {0:=()}, Phi a b = (a = false))
theorem w4c2_82 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_lookup_acc_impl 14 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (A := Bool) (B := Unit) (Φ := fun _ a _ => iprop(⌜a = false⌝))
    (m1 := sg false) (m2 := sg ()) (i := 0) (x1 := true) (x2 := ()) (sg_get ())
  exact Bool.false_ne_true (sp ((s2E _ _ _).2.trans (e.trans sep_elim_left)) 0 rfl).symm

-- `Iris.BI.BigSepM2.bigSepM2_affinely_pure_elim` idx 10: necessary (SiProp: m1 = {0:=()}, m2 empty (B = Empty))
theorem w4c2_83 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_affinely_pure_elim 10 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (A := Unit) (B := Empty) (fun _ _ _ => True) (m1 := sg ()) (m2 := ∅)
  exact sg_ne () (sp (e.trans (BigSepM2.bigSepM2_empty_left _ _)) 0 ⟨trivial, fun _ _ x2 => x2.elim⟩)

-- `Iris.BI.BigSepM2.bigSepM2_pure` idx 7: necessary (HeapProp Unit (not BIAffine): maps empty, phi = True; emp is not the pure True)
theorem w4c2_84 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_pure 7 := fun h => by
  have e := (h (PROP := HeapProp Unit) (M := TM) (K := Nat) (A := Unit) (B := Unit) (fun _ _ _ => True) ∅ ∅).2
  exact h0_ne (hp (e.trans (BigSepM2.bigSepM2_empty _).1) h0 ⟨fun _ => Iff.rfl, fun _ _ _ _ _ => trivial⟩)

-- `Iris.BI.BigSepM2.bigSepM2_persistently` idx 7: necessary (HeapProp Unit (not BIAffine): maps empty; pers emp holds everywhere)
theorem w4c2_85 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_persistently 7 := fun h => by
  have e := (h (PROP := HeapProp Unit) (M := TM) (K := Nat) (A := Unit) (B := Unit) (fun _ _ _ => iprop(True)) ∅ ∅).1
  exact h0_ne (hp ((persistently_mono (BigSepM2.bigSepM2_empty _).2).trans (e.trans (BigSepM2.bigSepM2_empty _).1)) h0 rfl)

-- `Iris.BI.BigSepM2.bigSepM2_intro` idx 10: necessary (SiProp: m1 = {0:=()}, m2 empty (B = Empty))
theorem w4c2_86 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_intro 10 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (A := Unit) (B := Empty) (fun _ _ _ => iprop(True)) (sg ()) ∅
  refine sg_ne () (sp (Entails.trans ?_ (e.trans (BigSepM2.bigSepM2_empty_left _ _))) 0 (show (iprop(emp) : SiProp).holds 0 from trivial))
  exact intuitionistically_emp.2.trans (intuitionistically_mono (forall_intro fun _ => forall_intro fun _ => forall_intro fun x => x.elim))

-- `Iris.BI.BigSepM2.bigSepM2_forall` idx 7: necessary (HeapProp Unit (not BIAffine): maps empty, Phi = True; True |- emp fails)
theorem w4c2_87 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_forall 7 := fun h => by
  have e := (h (PROP := HeapProp Unit) (M := TM) (K := Nat) (A := Unit) (B := Unit) (fun _ _ _ => iprop(True)) ∅ ∅
    (fun _ _ _ => pure_persistent True)).2
  exact not_true_emp ((and_intro (pure_intro fun _ => Iff.rfl)
    (forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => imp_intro (imp_intro (pure_intro trivial)))).trans
    (e.trans (BigSepM2.bigSepM2_empty _).1))

-- `Iris.BI.BigSepM2.bigSepM2_sepM_2` idx 11: necessary (SiProp: m1 = {0:=()}, m2 empty, Phi1 = Phi2 = True)
theorem w4c2_88 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_sepM_2 11 := fun h => by
  have e := h (PROP := SiProp) (M := TM) (K := Nat) (A := Unit) (B := Unit) (fun _ _ => iprop(True)) (fun _ _ => iprop(True)) (sg ()) ∅
  rw [sgE, emE] at e
  exact sg_ne () (sp ((sep_emp (P := iprop(True))).2.trans ((sep_mono_left e).trans (wand_elim_left.trans
    (BigSepM2.bigSepM2_empty_left _ _)))) 0 trivial)

-- `Iris.BI.BigSepM2.bigSepM2_dist_2` idx 16: necessary (SiProp, n = 0: m1 = {0:=()}, m1' empty, m2 = m2' = {0:=()}, Phi = Psi = True)
theorem w4c2_89 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_dist_2 16 := fun h => by
  have e := @h SiProp _ Nat TM _ Unit Unit _ _ (fun _ _ _ => iprop(True))
    (fun _ _ _ => iprop(True)) (sg ()) (sg ()) ∅ (sg ()) 0 (fun _ => orelD 0 _)
    (fun _ _ _ _ _ _ h1' => by rw [get?_empty] at h1'; cases h1')
  exact sg_ne () (sp (BigSepM2.bigSepM2_empty_right _ _) 0 ((e (Nat.le_refl 0)).1 (sp (s2E _ _ _).2 0 trivial)))

-- `Iris.BI.BigSepM2.bigSepM2_dist_2` idx 17: necessary (SiProp, n = 0: m1 = m1' = m2 = {0:=()}, m2' empty, Phi = Psi = True)
theorem w4c2_90 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_dist_2 17 := fun h => by
  have e := @h SiProp _ Nat TM _ Unit Unit _ _ (fun _ _ _ => iprop(True))
    (fun _ _ _ => iprop(True)) (sg ()) (sg ()) (sg ()) ∅ 0 (fun _ => orelD 0 _)
    (fun _ _ _ _ _ _ _ _ _ h2' => by rw [get?_empty] at h2'; cases h2')
  exact sg_ne () (sp (BigSepM2.bigSepM2_empty_left _ _) 0 ((e (Nat.le_refl 0)).1 (sp (s2E _ _ _).2 0 trivial)))

-- `Iris.BI.BigSepM2.bigSepM2_dist_2` idx 18: necessary (SiProp, n = 0: all four maps {0:=()}, Phi = True, Psi = False)
theorem w4c2_91 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_dist_2 18 := fun h => by
  have e := @h SiProp _ Nat TM _ Unit Unit _ _ (fun _ _ _ => iprop(True))
    (fun _ _ _ => iprop(False)) (sg ()) (sg ()) (sg ()) (sg ()) 0 (fun _ => orelD 0 _) (fun _ => orelD 0 _)
  exact sp (s2E _ _ _).1 0 ((e (Nat.le_refl 0)).1 (sp (s2E _ _ _).2 0 trivial))
-- `Iris.BI.BigSepS.bigSepS_mono` idx 8: necessary (SiProp: X = {0}, Phi = True, Psi = False)
theorem w4c2_92 : ¬ drop0% Iris.BI.BigSepS.bigSepS_mono 8 := fun h =>
  sp (((ssE _).2.trans (h (PROP := SiProp) (S := TS) (A := Nat) (Φ := fun _ => iprop(True))
    (Ψ := fun _ => iprop(False)) (X := {0}))).trans (ssE _).1) 0 trivial

-- `Iris.BI.BigSepS.bigSepS_ne` idx 9: necessary (SiProp, n = 0: X = {0}, Phi = True, Psi = False)
theorem w4c2_93 : ¬ drop0% Iris.BI.BigSepS.bigSepS_ne 9 := fun h => by
  have e := h (PROP := SiProp) (S := TS) (A := Nat) (Φ := fun _ => iprop(True)) (Ψ := fun _ => iprop(False)) (X := {0}) (n := 0)
  exact sp (ssE _).1 0 ((e (Nat.le_refl 0)).1 (sp (ssE _).2 0 trivial))

-- `Iris.BI.BigSepS.bigSepS_eq` idx 8: necessary (SiProp: X = {0}, Phi = True, Psi = False)
theorem w4c2_94 : ¬ drop0% Iris.BI.BigSepS.bigSepS_eq 8 := fun h => by
  have e := h (PROP := SiProp) (S := TS) (A := Nat) (Φ := fun _ => iprop(True)) (Ψ := fun _ => iprop(False)) (X := {0})
  exact sp (((ssE _).2.trans (BiEntails.of_eq e).1).trans (ssE _).1) 0 trivial

-- `Iris.BI.BigSepS.bigSepS_eqv` idx 8: necessary (SiProp: X = {0}, Phi = True, Psi = False)
theorem w4c2_95 : ¬ drop0% Iris.BI.BigSepS.bigSepS_eqv 8 := fun h =>
  sp (((ssE _).2.trans (h (PROP := SiProp) (S := TS) (A := Nat) (Φ := fun _ => iprop(True))
    (Ψ := fun _ => iprop(False)) (X := {0})).1).trans (ssE _).1) 0 trivial

-- `Iris.BI.BigSepS.bigSepS_mono_of_forall` idx 8: necessary (SiProp: X = {0}, Phi = True, Psi = False)
theorem w4c2_96 : ¬ drop0% Iris.BI.BigSepS.bigSepS_mono_of_forall 8 := fun h =>
  sp (((ssE _).2.trans (h (PROP := SiProp) (S := TS) (A := Nat) (Φ := fun _ => iprop(True))
    (Ψ := fun _ => iprop(False)) (X := {0}))).trans (ssE _).1) 0 trivial

-- `Iris.BI.BigSepS.bigSepS_flip_mono` idx 8: necessary (SiProp: X = {0}, Psi = True, Phi = False)
theorem w4c2_97 : ¬ drop0% Iris.BI.BigSepS.bigSepS_flip_mono 8 := fun h =>
  sp (((ssE _).2.trans (h (PROP := SiProp) (S := TS) (A := Nat) (Φ := fun _ => iprop(False))
    (Ψ := fun _ => iprop(True)) (X := {0}))).trans (ssE _).1) 0 trivial

-- `Iris.BI.BigSepS.bigSepS_empty_intro` idx 6: necessary (HeapProp Unit: P = True (not affine))
theorem w4c2_98 : ¬ drop0% Iris.BI.BigSepS.bigSepS_empty_intro 6 := fun h =>
  not_true_emp ((h (PROP := HeapProp Unit) (S := TS) (A := Nat) (P := iprop(True)) (Φ := fun _ => iprop(True))).trans (seE _).1)

-- `Iris.BI.BigSepS.bigSepS_insert` idx 8: necessary (HeapProp Unit: X = {0}, x = 0, Phi = owns cell 0)
theorem w4c2_99 : ¬ drop0% Iris.BI.BigSepS.bigSepS_insert 8 := fun h => by
  have e := (h (PROP := HeapProp Unit) (S := TS) (A := Nat) (Φ := fun _ => own0) (X := {0}) (x := 0)).1
  rw [insS] at e
  exact own0_sep_own0 (hp (((ssE _).2.trans e).trans (sep_mono_right (ssE _).1)) h0 own0_h0)

-- `_private.Iris.BI.BigOp.BigSepSet.0.Iris.BI.BigSepS.mem_of_getElem?` idx 6: necessary (X empty: nothing is a member)
theorem w4c2_100 : ¬ drop0% _private.Iris.BI.BigOp.BigSepSet.«0».Iris.BI.BigSepS.mem_of_getElem? 6 := fun h =>
  LawfulSet.mem_empty (@h TS Nat _ 0 0 ∅)

-- `Iris.BI.BigSepS.bigSepS_persistent` idx 7: necessary (HeapProp Unit: X = {0}, Phi = owns cell 0)
theorem w4c2_101 : ¬ drop0% Iris.BI.BigSepS.bigSepS_persistent 7 := fun h =>
  hp ((ssE _).2.trans ((h (PROP := HeapProp Unit) (S := TS) (A := Nat) (Φ := fun _ => own0) (X := {0})).persistent.trans
    (persistently_mono (ssE _).1))) h0 own0_h0 rfl

-- `Iris.BI.BigSepS.bigSepS_persistent_inst` idx 7: necessary (HeapProp Unit: X = {0}, Phi = owns cell 0)
theorem w4c2_102 : ¬ drop0% Iris.BI.BigSepS.bigSepS_persistent_inst 7 := fun h =>
  hp ((ssE _).2.trans ((h (PROP := HeapProp Unit) (S := TS) (A := Nat) (Φ := fun _ => own0) (X := {0})).persistent.trans
    (persistently_mono (ssE _).1))) h0 own0_h0 rfl

-- `Iris.BI.BigSepS.bigSepS_affine` idx 7: necessary (HeapProp Unit: X = {0}, Phi = True)
theorem w4c2_103 : ¬ drop0% Iris.BI.BigSepS.bigSepS_affine 7 := fun h =>
  not_true_emp ((ssE _).2.trans (h (PROP := HeapProp Unit) (S := TS) (A := Nat) (Φ := fun _ => iprop(True)) (X := {0})).affine)

-- `Iris.BI.BigSepS.bigSepS_affine_inst` idx 7: necessary (HeapProp Unit: X = {0}, Phi = True)
theorem w4c2_104 : ¬ drop0% Iris.BI.BigSepS.bigSepS_affine_inst 7 := fun h =>
  not_true_emp ((ssE _).2.trans (h (PROP := HeapProp Unit) (S := TS) (A := Nat) (Φ := fun _ => iprop(True)) (X := {0})).affine)

-- `Iris.BI.BigSepS.bigSepS_timeless` idx 8: necessary (SiProp: X = {0}, Phi = s0, true only at step 0)
theorem w4c2_105 : ¬ drop0% Iris.BI.BigSepS.bigSepS_timeless 8 := fun h =>
  s0_not_timeless (ssE _) (h (PROP := SiProp) (S := TS) (A := Nat) (Φ := fun _ => s0) (X := {0})).timeless

-- `Iris.BI.BigSepS.bigSepS_timeless_inst` idx 8: necessary (SiProp: X = {0}, Phi = s0, true only at step 0)
theorem w4c2_106 : ¬ drop0% Iris.BI.BigSepS.bigSepS_timeless_inst 8 := fun h =>
  s0_not_timeless (ssE _) (h (PROP := SiProp) (S := TS) (A := Nat) (Φ := fun _ => s0) (X := {0})).timeless

-- `Iris.BI.BigSepS.bigSepS_elem_of` idx 8: necessary (SiProp: X empty, x = 0, Phi = False)
theorem w4c2_107 : ¬ drop0% Iris.BI.BigSepS.bigSepS_elem_of 8 := fun h =>
  sp ((seE _).2.trans (h (PROP := SiProp) (S := TS) (A := Nat) (Φ := fun _ => iprop(False)) (X := ∅) (x := 0))) 0 trivial

-- `Iris.BI.BigSepS.bigSepS_elem_of` idx 9: necessary (HeapProp Unit: X = {0,1}, x = 0, Phi 0 = emp, Phi 1 = True (not affine))
theorem w4c2_108 : ¬ drop0% Iris.BI.BigSepS.bigSepS_elem_of 9 := fun h => by
  have e := h (PROP := HeapProp Unit) (S := TS) (A := Nat) (Φ := fun y => if y = 0 then iprop(emp) else iprop(True))
    (X := @Insert.insert Nat TS LawfulSet.instInsert 1 {0}) (x := 0) (LawfulSet.mem_insert.2 (Or.inr mem0))
  have := hp ((s01 _).2.trans e) h0 ⟨h0, ∅, (union_comm.trans empty_union.symm).symm, fun _ => Or.inr rfl, trivial,
    by simp only [↓reduceIte]; rfl⟩
  exact h0_ne this

-- `Iris.BI.BigSepS.bigSepS_elem_of_acc` idx 8: necessary (SiProp: X empty, x = 0, Phi = False)
theorem w4c2_109 : ¬ drop0% Iris.BI.BigSepS.bigSepS_elem_of_acc 8 := fun h =>
  sp ((seE _).2.trans ((h (PROP := SiProp) (S := TS) (A := Nat) (Φ := fun _ => iprop(False)) (X := ∅) (x := 0)).trans
    sep_elim_left)) 0 trivial

-- `Iris.BI.BigSepS.bigSepS_pure` idx 5: necessary (HeapProp Unit (not BIAffine): X empty, phi = True)
theorem w4c2_110 : ¬ drop0% Iris.BI.BigSepS.bigSepS_pure 5 := fun h =>
  h0_ne (hp ((h (PROP := HeapProp Unit) (S := TS) (A := Nat) (φ := fun _ => True) (X := ∅)).2.trans (seE _).1) h0
    (fun _ _ => trivial))

-- `Iris.BI.BigSepS.bigSepS_intro` idx 8: necessary (HeapProp Unit: X empty, P = True (not intuitionistic))
theorem w4c2_111 : ¬ drop0% Iris.BI.BigSepS.bigSepS_intro 8 := fun h =>
  not_true_emp ((h (PROP := HeapProp Unit) (S := TS) (A := Nat) (P := iprop(True)) (Φ := fun _ => iprop(True)) (X := ∅)
    (fun _ => .rfl)).trans (seE _).1)

-- `Iris.BI.BigSepS.bigSepS_intro` idx 9: necessary (SiProp: X = {0}, P = emp, Phi = False)
theorem w4c2_112 : ¬ drop0% Iris.BI.BigSepS.bigSepS_intro 9 := fun h =>
  sp ((h (PROP := SiProp) (S := TS) (A := Nat) (P := iprop(emp)) (Φ := fun _ => iprop(False)) (X := {0})).trans (ssE _).1) 0 trivial

-- `Iris.BI.BigSepS.bigSepS_forall` idx 5: necessary (HeapProp Unit (not BIAffine): X empty, Phi = True)
theorem w4c2_113 : ¬ drop0% Iris.BI.BigSepS.bigSepS_forall 5 := fun h =>
  not_true_emp ((forall_intro fun _ => imp_intro and_elim_l).trans
    ((h (PROP := HeapProp Unit) (S := TS) (A := Nat) (Φ := fun _ => iprop(True)) (X := ∅) (hPers := fun _ => pure_persistent True)).2.trans
     (seE _).1))

-- `Iris.BI.BigSepS.bigSepS_elem_of_acc_impl` idx 8: necessary (SiProp: X empty, x = 0, Phi = False)
theorem w4c2_114 : ¬ drop0% Iris.BI.BigSepS.bigSepS_elem_of_acc_impl 8 := fun h =>
  sp ((seE _).2.trans ((h (PROP := SiProp) (S := TS) (A := Nat) (Φ := fun _ => iprop(False)) (X := ∅) (x := 0)).trans
    sep_elim_left)) 0 trivial

-- `Iris.BI.BigSepS.bigSepS_persistently` idx 5: necessary (HeapProp Unit (not BIAffine): X empty; pers emp holds everywhere)
theorem w4c2_115 : ¬ drop0% Iris.BI.BigSepS.bigSepS_persistently 5 := fun h =>
  h0_ne (hp ((persistently_mono (seE _).2).trans ((h (PROP := HeapProp Unit) (S := TS) (A := Nat) (Φ := fun _ => iprop(True))
    (X := ∅)).1.trans (seE _).1)) h0 rfl)

-- `Iris.BI.BigSepS.bigSepS_subseteq` idx 8: necessary (HeapProp Unit: X = {0}, Y empty, Phi = True (not affine))
theorem w4c2_116 : ¬ drop0% Iris.BI.BigSepS.bigSepS_subseteq 8 := fun h =>
  not_true_emp (((ssE _).2.trans (h (PROP := HeapProp Unit) (S := TS) (A := Nat) (Φ := fun _ => iprop(True)) (X := {0}) (Y := ∅)
    LawfulSet.empty_subset)).trans (seE _).1)

-- `Iris.BI.BigSepS.bigSepS_subseteq` idx 9: necessary (SiProp: X empty, Y = {0}, Phi = False)
theorem w4c2_117 : ¬ drop0% Iris.BI.BigSepS.bigSepS_subseteq 9 := fun h =>
  sp (((seE _).2.trans (h (PROP := SiProp) (S := TS) (A := Nat) (Φ := fun _ => iprop(False)) (X := ∅) (Y := {0}))).trans
    (ssE _).1) 0 trivial

-- `Iris.BI.BigSepS.bigSepS_of_list` idx 7: necessary (HeapProp Unit: l = [0, 0], Phi = owns cell 0)
theorem w4c2_118 : ¬ drop0% Iris.BI.BigSepS.bigSepS_of_list 7 := fun h => by
  have e := (h (PROP := HeapProp Unit) (S := TS) (A := Nat) (Φ := fun _ => own0) (l := [0, 0])).1
  have hk : (LawfulSet.ofList [0, 0] : TS) = {0} := LawfulSet.ext fun x =>
    (LawfulSet.mem_ofList (S := TS)).symm.trans (by rw [LawfulSet.mem_singleton]; simp)
  exact own0_sep_own0 (hp (((ssE _).2.trans (BiEntails.of_eq (congrArg (bigSepS (fun _ => own0)) hk)).2).trans (e.trans (BigSepL.bigSepL_cons.1.trans (sep_mono_right BigSepL.bigSepL_singleton.1)))) h0 own0_h0)

-- `Iris.BI.BigSepS.bigSepS_filter` idx 5: necessary (HeapProp Unit (not BIAffine): X = {0}, phi = false, Phi = True)
theorem w4c2_119 : ¬ drop0% Iris.BI.BigSepS.bigSepS_filter 5 := fun h => by
  have e := (BigSepS.bigSepS_filter_cond _).symm.trans (h (PROP := HeapProp Unit) (S := TS) (A := Nat) (fun _ => false)
    (Φ := fun _ => iprop(True)) (X := {0}))
  exact h0_ne (hp (((ssE _).2.trans e.2).trans (ssE _).1) h0 (fun _ => trivial))

-- `Iris.BI.BigSepS.bigSepS_filter_acc` idx 9: necessary (SiProp: X empty, Y = {0}, phi = true, Phi = False)
theorem w4c2_120 : ¬ drop0% Iris.BI.BigSepS.bigSepS_filter_acc 9 := fun h =>
  sp ((seE _).2.trans ((h (PROP := SiProp) (S := TS) (A := Nat) (fun _ => true) (Φ := fun _ => iprop(False)) (X := ∅) (Y := {0})).trans
    (sep_elim_left.trans ((BigSepS.bigSepS_filter_cond _).1.trans (ssE _).1)))) 0 trivial

-- `Iris.BI.BigSepS.bigSepS_split_subset` idx 8: necessary (SiProp: X empty, Y = {0}, Phi = False)
theorem w4c2_121 : ¬ drop0% Iris.BI.BigSepS.bigSepS_split_subset 8 := fun h =>
  sp ((seE _).2.trans ((h (PROP := SiProp) (S := TS) (A := Nat) (Φ := fun _ => iprop(False)) (X := ∅) (Y := {0})).1.trans
    (sep_elim_left.trans (ssE _).1))) 0 trivial

-- `Iris.BI.BigSepS.bigSepS_delete_elim` idx 8: necessary (HeapProp Unit: X empty, x = 0, Phi = True (not affine))
theorem w4c2_122 : ¬ drop0% Iris.BI.BigSepS.bigSepS_delete_elim 8 := fun h => by
  have e := h (PROP := HeapProp Unit) (S := TS) (A := Nat) (Φ := fun _ => iprop(True)) (X := ∅) (x := 0)
  rw [edS] at e
  exact not_true_emp ((sep_emp (P := iprop(True))).2.trans ((sep_mono e (seE _).2).trans (wand_elim_left.trans (seE _).1)))

-- `Iris.BI.BigSepS.bigSepS_fn_insert` idx 12: necessary (SiProp: X = {0}, x = 0, B = Bool, b = true, f = false, Psi y c = (c = true))
theorem w4c2_123 : ¬ drop0% Iris.BI.BigSepS.bigSepS_fn_insert 12 := fun h => by
  have e := (h (PROP := SiProp) (S := TS) (A := Nat) (B := Bool) (Ψ := fun _ c => iprop(⌜c = true⌝)) (f := fun _ => false)
    (X := {0}) (x := 0) (b := true)).1
  rw [insS] at e
  exact Bool.false_ne_true (sp (((ssE _).2.trans e).trans (sep_elim_right.trans (ssE _).1)) 0 rfl)

-- `Iris.BI.BigSepS.bigSepS_fn_insert_key` idx 10: necessary (SiProp: X = {0}, x = 0, P = True, Phi = False)
theorem w4c2_124 : ¬ drop0% Iris.BI.BigSepS.bigSepS_fn_insert_key 10 := fun h => by
  have e := (h (PROP := SiProp) (S := TS) (A := Nat) (Φ := fun _ => iprop(False)) (X := {0}) (x := 0) (P := iprop(True))).1
  rw [insS] at e
  exact sp (((ssE _).2.trans e).trans (sep_elim_right.trans (ssE _).1)) 0 trivial

-- `Iris.BI.BigSepS.bigSepS_dup` idx 6: necessary (HeapProp Unit: P = True (not affine), X empty)
theorem w4c2_125 : ¬ drop0% Iris.BI.BigSepS.bigSepS_dup 6 := fun h => by
  have := hp ((h (PROP := HeapProp Unit) (S := TS) (A := Nat) (P := iprop(True)) (X := ∅)).trans
    (wand_mono_right (wand_mono_right (seE _).1))) ∅ rfl ∅ empty_disjoint
    ⟨rfl, fun σ' _ _ => ⟨∅, ∅ ∪ σ', empty_union, empty_disjoint, trivial, trivial⟩⟩ h0 (fun _ => Or.inl rfl) trivial
  have e := congrFun this 0
  simp [h0, Union.union, EmptyCollection.emptyCollection] at e
-- `Iris.BI.BigSepM.bigSepM_later` idx 8: necessary (UPred B2, a non-affine BI where later emp is not emp: m empty)
theorem w4c2_126 : ¬ drop0% Iris.BI.BigSepM.bigSepM_later 8 := fun h => by
  have e := (h (PROP := UPred B2) (M := TM) (K := Nat) (V := Unit) (Φ := fun _ _ => iprop(True)) (m := ∅)).1
  rw [emE, emE] at e
  exact b2_later_emp e

-- `Iris.BI.BigSepM.bigSepM_laterN` idx 9: necessary (UPred B2, a non-affine BI where later emp is not emp: m empty, n = 1)
theorem w4c2_127 : ¬ drop0% Iris.BI.BigSepM.bigSepM_laterN 9 := fun h => by
  have e := (h (PROP := UPred B2) (M := TM) (K := Nat) (V := Unit) (Φ := fun _ _ => iprop(True)) (m := ∅) (n := 1)).1
  rw [emE, emE] at e
  exact b2_later_emp e

-- `Iris.BI.BigSepS.bigSepS_later` idx 5: necessary (UPred B2, a non-affine BI where later emp is not emp: X empty)
theorem w4c2_128 : ¬ drop0% Iris.BI.BigSepS.bigSepS_later 5 := fun h =>
  b2_later_emp ((later_mono (seE _).2).trans
    ((h (PROP := UPred B2) (S := TS) (A := Nat) (Φ := fun _ => iprop(True)) (X := ∅)).1.trans (seE _).1))

-- `Iris.BI.BigSepS.bigSepS_laterN` idx 5: necessary (UPred B2, a non-affine BI where later emp is not emp: X empty, n = 1)
theorem w4c2_129 : ¬ drop0% Iris.BI.BigSepS.bigSepS_laterN 5 := fun h =>
  b2_later_emp ((later_mono (seE _).2).trans
    ((h (PROP := UPred B2) (S := TS) (A := Nat) (Φ := fun _ => iprop(True)) (X := ∅) (n := 1)).1.trans (seE _).1))
-- `Iris.BI.BigSepM2.bigSepM2_closed` idx 11: removable (derivable: BI.equiv_iff makes bi-entailment equality, so every predicate respects it)
theorem w4c2_130 : drop% Iris.BI.BigSepM2.bigSepM2_closed 11 := by
  intro PROP _ K A B M _ P Φ m1 m2 hemp hfalse hsep h
  exact BigSepM2.bigSepM2_closed P Φ m1 m2 (fun e => (BiEntails.to_eq e) ▸ Iff.rfl) hemp hfalse hsep h

-- helper: heaps owning exactly cell 1 / exactly cells 0 and 1
def h1 : State Unit := fun i => if i = 1 then result () else unknown
-- helper
def h01 : State Unit := fun i => if i = 0 ∨ i = 1 then result () else unknown
-- helper: exact ownership of cell 0 / of cell 1 (both persistent, as they hold at the empty heap too)
def e0 : HeapProp Unit := fun σ => σ = ∅ ∨ σ = h0
-- helper
def e1 : HeapProp Unit := fun σ => σ = ∅ ∨ σ = h1

-- `Iris.BI.BigSepM.bigSepM_forall_intro` idx 8: necessary (HeapProp Unit (not BIAffine): m = {0:=(),1:=()}, Phi 0 = heap empty or exactly cell 0, Phi 1 = heap empty or exactly cell 1 (both persistent); their separating conjunction holds on cells 0,1 where neither holds)
theorem w4c2_131 : ¬ drop0% Iris.BI.BigSepM.bigSepM_forall_intro 8 := fun h => by
  have e := @h (HeapProp Unit) _ Nat Unit TM _ (fun k _ => if k = 0 then e0 else e1) (tw () ())
    (fun k _ => ⟨fun σ _ => by by_cases hk : k = 0 <;> simp only [hk, ↓reduceIte] <;> exact Or.inl rfl⟩)
  rw [twE] at e
  have hs : iprop((if (1:Nat) = 0 then e0 else e1) ∗ (if (0:Nat) = 0 then e0 else e1)) h01 := by
    refine ⟨h1, h0, ?_, ?_, Or.inr rfl, Or.inr rfl⟩
    · funext i; simp only [h01, h1, h0, Union.union]
      by_cases a : i = 0 <;> by_cases b : i = 1 <;> simp_all
    · intro i; by_cases a : i = 1 <;> simp_all [h1, h0]
  have := hp (e.trans ((forall_elim 0).trans ((forall_elim ()).trans
    (pure_imp_elim ((get?_insert_ne (by decide)).trans (get?_insert_eq rfl)))))) h01 hs
  rcases this with c | c
  · have := congrFun c 0; simp [h01, EmptyCollection.emptyCollection] at this
  · have := congrFun c 1; simp [h01, h0] at this

-- helper: two keys present in m1 are disjointness-incompatible with both halves covering key 0
theorem uinv {A B : Type} (m1' m2' : TM B) (hD : PartialMap.disjoint m1' m2')
    (d1 : ∀ k, (get? (sg (() : Unit)) k).isSome = true ↔ (get? m1' k).isSome = true)
    (d2 : ∀ k, (get? (sg (() : Unit)) k).isSome = true ↔ (get? m2' k).isSome = true) : False :=
  hD 0 ⟨(d1 0).1 (by rw [sg_get]; rfl), (d2 0).1 (by rw [sg_get]; rfl)⟩

-- `Iris.BI.BigSepM2.bigSepM2_union_inv_left` idx 12: necessary (SiProp: m1 = m2 = m' = {0:=()}, Phi = True; m' cannot be split into two disjoint maps both covering key 0)
theorem w4c2_132 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_union_inv_left 12 := fun h => by
  have e := @h SiProp _ Nat Unit Unit TM _ _ (fun _ _ _ => iprop(True)) (sg ()) (sg ()) (sg ())
  rw [unionSelf] at e
  refine sp (Q := iprop(False)) ((s2E _ _ _).2.trans (e.trans (exists_elim fun m1' => exists_elim fun m2' =>
    pure_elim_left fun _ => pure_elim_left fun hD =>
    (sep_mono BigSepM2.bigSepM2_lookup_iff BigSepM2.bigSepM2_lookup_iff).trans (pure_sep.1.trans
    (pure_elim' fun ⟨d1, d2⟩ => (uinv (A := Unit) m1' m2' hD d1 d2).elim))))) 0 trivial

-- `Iris.BI.BigSepM2.bigSepM2_union_inv_right` idx 12: necessary (SiProp: m1 = m2 = m' = {0:=()}, Phi = True; m' cannot be split into two disjoint maps both covering key 0)
theorem w4c2_133 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_union_inv_right 12 := fun h => by
  have e := @h SiProp _ Nat Unit Unit TM _ _ (fun _ _ _ => iprop(True)) (sg ()) (sg ()) (sg ())
  rw [unionSelf] at e
  refine sp (Q := iprop(False)) ((s2E _ _ _).2.trans (e.trans (exists_elim fun m1' => exists_elim fun m2' =>
    pure_elim_left fun _ => pure_elim_left fun hD =>
    (sep_mono BigSepM2.bigSepM2_lookup_iff BigSepM2.bigSepM2_lookup_iff).trans (pure_sep.1.trans
    (pure_elim' fun ⟨d1, d2⟩ => (uinv (A := Unit) m1' m2' hD (fun k => (d1 k).symm) (fun k => (d2 k).symm)).elim))))) 0 trivial

-- helper: exactly cell 0 / exactly cell 1
def x0 : HeapProp Unit := fun σ => σ = h0
-- helper
def x1 : HeapProp Unit := fun σ => σ = h1
-- helper
theorem sep_x1_x0 : iprop(x1 ∗ x0) h01 := by
  refine ⟨h1, h0, ?_, ?_, rfl, rfl⟩
  · funext i; simp only [h01, h1, h0, Union.union]
    by_cases a : i = 0 <;> by_cases b : i = 1 <;> simp_all
  · intro i; by_cases a : i = 1 <;> simp_all [h1, h0]

-- `Iris.BI.BigSepM2.bigSepM2_closed` idx 14: necessary (HeapProp Unit: P = equal to emp, False, exactly-cell-0 or exactly-cell-1; m1 = m2 = {0:=(),1:=()}, Phi k = exactly cell k; the result owns both cells)
theorem w4c2_134 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_closed 14 := fun h => by
  have r := @h (HeapProp Unit) _ Nat Unit Unit TM _
    (fun Q => Q = iprop(emp) ∨ Q = iprop(False) ∨ Q = x0 ∨ Q = x1)
    (fun k _ _ => if k = 0 then x0 else x1) (tw () ()) (tw () ())
    (fun e => (BiEntails.to_eq e) ▸ Iff.rfl) (Or.inl rfl) (Or.inr (Or.inl rfl))
    (fun {k} _ _ => by by_cases hk : k = 0 <;> simp [hk])
  have eq : bigSepM2 (fun k (_ : Unit) (_ : Unit) => if k = 0 then x0 else x1) (tw () ()) (tw () ()) = iprop(x1 ∗ x0) :=
    BiEntails.to_eq ((BigSepM2.bigSepM2_insert ((get?_insert_ne (by decide)).trans (get?_empty 1))
      ((get?_insert_ne (by decide)).trans (get?_empty 1))).trans ⟨sep_mono_right (s2E (fun k (_ : Unit) (_ : Unit) => if k = 0 then x0 else x1) () ()).1,
       sep_mono_right (s2E (fun k (_ : Unit) (_ : Unit) => if k = 0 then x0 else x1) () ()).2⟩)
  rw [eq] at r
  have hs := sep_x1_x0
  rcases r with c | c | c | c <;> rw [c] at hs
  · have := congrFun hs 0; simp [h01, EmptyCollection.emptyCollection] at this
  · exact hs
  · have := congrFun hs 1; simp [h01, h0] at this
  · have := congrFun hs 0; simp [h01, h1] at this
-- helper: three-element monoid (e unit, a • a = t, t absorbing) with the extension order: an affine UORA where a is not duplicable
inductive A3 | e | a | t deriving DecidableEq
-- helper
def A3.op : A3 → A3 → A3
  | .e, y => y
  | x, .e => x
  | _, _ => .t
-- helper
def A3.le : A3 → A3 → Bool
  | .e, _ => true
  | _, .t => true
  | .a, .a => true
  | _, _ => false
-- helper
instance : OFE A3 := OFE.ofDiscrete A3
-- helper
instance : OFE.Discrete A3 := ⟨id⟩
-- helper
instance instORAA3 : ORA A3 := ORA.ofDiscreteORAData {
  pcore := fun _ => some .e
  op := A3.op
  Valid := fun _ => True
  Order := fun x y => A3.le x y = true
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
  pcore_op_left := by intro x cx h; cases h; cases x <;> rfl
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := fun _ _ _ => trivial
  ord_trans := by intro x y z h1 h2; cases x <;> cases y <;> cases z <;> simp_all [A3.le]
  op_mono_left := by intro x y z h; cases x <;> cases y <;> cases z <;> simp_all [A3.le, A3.op]
  valid_of_ord := fun _ _ _ _ => trivial
  pcore_mono := by intro x y cx h1 h2; exact ⟨.e, rfl, by cases h2; rfl⟩
  pcore_order_op := by intro x cx h y; exact ⟨.e, rfl, by cases h; rfl⟩
  pcore_increasing := by intro x cx h y; cases h; cases y <;> rfl
  increasing_closed := by intro x y hx h z; cases y <;> cases z <;> rfl }
-- helper
instance : OrderRefl A3 := ⟨fun x => by cases x <;> rfl⟩
-- helper
instance instUORAA3 : UORA A3 where
  unit := .e
  unit_valid := trivial
  unit_left_id := rfl
  pcore_unit := rfl
-- helper
instance : IncOrd A3 := ⟨by
  intro x y ⟨z, hz⟩
  cases x <;> cases z <;> (subst hz; rfl)⟩
-- helper: in UPred A3, ownM a does not entail ownM a ∗ ownM a
theorem a3_not_dup (e : (UPred.ownM A3.a : UPred A3) ⊢ iprop(UPred.ownM A3.a ∗ UPred.ownM A3.a)) : False := by
  have := (e.trans (UPred.ownM_op A3.a A3.a).2) 0 ⟨A3.a, trivial⟩ (by show A3.le .a .a = true; rfl)
  have h2 : A3.le .t .a = true := this
  exact absurd h2 (by decide)


-- `Iris.BI.BigSepS.bigSepS_forall` idx 8: necessary (UPred A3 (affine, a • a = t): X = {0,1}, Phi = ownM a, not persistent; the conjunction does not split)
theorem w4c2_135 : ¬ drop0% Iris.BI.BigSepS.bigSepS_forall 8 := fun h =>
  a3_not_dup ((forall_intro fun _ => imp_intro and_elim_l).trans
    ((h (PROP := UPred A3) (S := TS) (A := Nat) (Φ := fun _ => UPred.ownM A3.a)
      (X := @Insert.insert Nat TS LawfulSet.instInsert 1 {0})).2.trans (s01 _).1))

-- `Iris.BI.BigSepM2.bigSepM2_forall` idx 11: necessary (UPred A3 (affine, a • a = t): m1 = m2 = {0:=(),1:=()}, Phi = ownM a, not persistent)
theorem w4c2_136 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_forall 11 := fun h => by
  have e := (@h (UPred A3) _ Nat Unit Unit TM _ _ (fun _ _ _ => UPred.ownM A3.a) (tw () ()) (tw () ())).2
  have eq : bigSepM2 (fun _ (_ : Unit) (_ : Unit) => (UPred.ownM A3.a : UPred A3)) (tw () ()) (tw () ()) ⊢
      iprop(UPred.ownM A3.a ∗ UPred.ownM A3.a) :=
    (BigSepM2.bigSepM2_insert ((get?_insert_ne (by decide)).trans (get?_empty 1))
      ((get?_insert_ne (by decide)).trans (get?_empty 1))).1.trans (sep_mono_right (s2E _ _ _).1)
  exact a3_not_dup ((and_intro (pure_intro fun _ => Iff.rfl)
    (forall_intro fun _ => forall_intro fun _ => forall_intro fun _ => imp_intro (imp_intro (and_elim_l.trans and_elim_l)))).trans
    (e.trans eq))
-- helper: a step-indexed BI over the resource monoid (Bool, or, false) whose two resources agree at step 0;
-- emp holds at step 0 everywhere but later only at the unit, so emp is not timeless
structure TP where
  h : Nat → Bool → Prop
  closed : ∀ {n m r}, h n r → m ≤ n → h m r
  ne0 : ∀ {r r'}, h 0 r → h 0 r'
-- helper
instance tpOFE : OFE TP where
  Dist n P Q := ∀ {m}, m ≤ n → ∀ r, (P.h m r ↔ Q.h m r)
  dist_eqv := ⟨fun _ {_} _ _ => Iff.rfl, fun h _ hle r => (h hle r).symm, fun h₁ h₂ _ hle r => (h₁ hle r).trans (h₂ hle r)⟩
  eq_dist' {P Q} := by
    refine ⟨?_, fun h => ?_⟩
    · rintro rfl _ _ _ _; exact Iff.rfl
    · obtain ⟨ph, _, _⟩ := P; obtain ⟨qh, _, _⟩ := Q
      have : ph = qh := funext fun n => funext fun r => propext (h n (Nat.le_refl n) r)
      subst this; rfl
  dist_lt h hlt _ hle r := h (by omega) r
-- helper
instance tpCOFE : IsCOFE TP where
  compl c := {
    h n r := (c n).h n r
    closed {n₁ _ _} h hle := (c.cauchy hle (Nat.le_refl _) _).mp ((c n₁).closed h hle)
    ne0 h := (c 0).ne0 h }
  conv_compl {_ c} _ hle r := (c.cauchy hle (Nat.le_refl _) r).symm
-- helper
def TP.sep (P Q : TP) : TP where
  h n r := ∃ r1 r2, (n = 0 ∨ r = or r1 r2) ∧ P.h n r1 ∧ Q.h n r2
  closed := fun ⟨r1, r2, e, h1, h2⟩ hle => ⟨r1, r2, e.imp_left (fun _ => by omega), P.closed h1 hle, Q.closed h2 hle⟩
  ne0 := fun ⟨r1, r2, _, h1, h2⟩ => ⟨r1, r2, .inl rfl, h1, h2⟩
-- helper
def TP.later (P : TP) : TP where
  h n r := match n with | 0 => True | k+1 => P.h k r
  closed {n m r} h hle := by
    cases m with
    | zero => trivial
    | succ m => cases n with
      | zero => omega
      | succ n => exact P.closed h (by omega)
  ne0 _ := trivial
-- helper
instance tpBase : BIBase TP where
  Entails P Q := ∀ n r, P.h n r → Q.h n r
  emp := ⟨fun n r => n = 0 ∨ r = false, fun {n m r} h hle => h.imp (fun _ => by omega) id, fun _ => .inl rfl⟩
  pure φ := ⟨fun _ _ => φ, fun h _ => h, fun h => h⟩
  and P Q := ⟨fun n r => P.h n r ∧ Q.h n r, fun h hle => ⟨P.closed h.1 hle, Q.closed h.2 hle⟩, fun h => ⟨P.ne0 h.1, Q.ne0 h.2⟩⟩
  or P Q := ⟨fun n r => P.h n r ∨ Q.h n r, fun h hle => h.imp (P.closed · hle) (Q.closed · hle), fun h => h.imp P.ne0 Q.ne0⟩
  imp P Q := ⟨fun n r => ∀ m, m ≤ n → P.h m r → Q.h m r, fun h hle m hm hp => h m (by omega) hp,
    fun h m hm hp => by cases (show m = 0 by omega); exact Q.ne0 (h 0 (Nat.le_refl 0) (P.ne0 hp))⟩
  sForall Ψ := ⟨fun n r => ∀ p, Ψ p → p.h n r, fun h hle p hp => p.closed (h p hp) hle, fun h p hp => p.ne0 (h p hp)⟩
  sExists Ψ := ⟨fun n r => ∃ p, Ψ p ∧ p.h n r, fun ⟨p, hp, h⟩ hle => ⟨p, hp, p.closed h hle⟩, fun ⟨p, hp, h⟩ => ⟨p, hp, p.ne0 h⟩⟩
  sep := TP.sep
  wand P Q := ⟨fun n r => ∀ m, m ≤ n → ∀ r', P.h m r' → Q.h m (or r r'), fun h hle m hm r' hp => h m (by omega) r' hp,
    fun h m hm r' hp => by cases (show m = 0 by omega); exact Q.ne0 (h 0 (Nat.le_refl 0) r' hp)⟩
  persistently P := ⟨fun n _ => P.h n false, fun h hle => P.closed h hle, fun h => h⟩
  later := TP.later
-- helper
instance tpBI : BI TP where
  entails_refl _ _ h := h
  entails_trans h1 h2 n r h := h2 n r (h1 n r h)
  equiv_iff := OFE.eq_dist.trans
    ⟨fun heq => ⟨fun n r hP => (heq n (Nat.le_refl n) r).mp hP, fun n r hQ => (heq n (Nat.le_refl n) r).mpr hQ⟩,
     fun H _ _ _ r => ⟨H.1 _ r, H.2 _ r⟩⟩
  and_ne.ne _ _ _ h₁ _ _ h₂ m hle r := ⟨.imp (h₁ hle r).mp (h₂ hle r).mp, .imp (h₁ hle r).mpr (h₂ hle r).mpr⟩
  or_ne.ne _ _ _ h₁ _ _ h₂ m hle r := ⟨.imp (h₁ hle r).mp (h₂ hle r).mp, .imp (h₁ hle r).mpr (h₂ hle r).mpr⟩
  imp_ne.ne _ _ _ h₁ _ _ h₂ m hle r := {
    mp := fun hpq n' hn' hP => (h₂ (m := n') (by omega) r).mp (hpq n' hn' ((h₁ (m := n') (by omega) r).mpr hP))
    mpr := fun hpq n' hn' hP => (h₂ (m := n') (by omega) r).mpr (hpq n' hn' ((h₁ (m := n') (by omega) r).mp hP)) }
  sForall_ne {_ _ _} H _ hle r := by
    refine ⟨fun h Q hQ => ?_, fun h P hP => ?_⟩
    · obtain ⟨P, hP, hPQ⟩ := H.2 _ hQ
      exact (hPQ hle r).mp (h _ hP)
    · obtain ⟨Q, hQ, hPQ⟩ := H.1 P hP
      exact (hPQ hle r).mpr (h _ hQ)
  sExists_ne {_ _ _} H m hle r := by
    refine ⟨?_, ?_⟩
    · rintro ⟨P, hP, hPm⟩
      obtain ⟨Q, hQ, hPQ⟩ := H.1 P hP
      exact ⟨Q, hQ, (hPQ hle r).mp hPm⟩
    · rintro ⟨Q, hQ, hQm⟩
      obtain ⟨P, hP, hPQ⟩ := H.2 Q hQ
      exact ⟨P, hP, (hPQ hle r).mpr hQm⟩
  sep_ne.ne _ _ _ h₁ _ _ h₂ m hle r :=
    ⟨fun ⟨r1, r2, e, a, b⟩ => ⟨r1, r2, e, (h₁ hle r1).mp a, (h₂ hle r2).mp b⟩,
     fun ⟨r1, r2, e, a, b⟩ => ⟨r1, r2, e, (h₁ hle r1).mpr a, (h₂ hle r2).mpr b⟩⟩
  wand_ne.ne _ _ _ h₁ _ _ h₂ m hle r :=
    ⟨fun hw n' hn' r' hP => (h₂ (m := n') (by omega) _).mp (hw n' hn' r' ((h₁ (m := n') (by omega) r').mpr hP)),
     fun hw n' hn' r' hP => (h₂ (m := n') (by omega) _).mpr (hw n' hn' r' ((h₁ (m := n') (by omega) r').mp hP))⟩
  persistently_ne.ne _ _ _ h m hle r := h hle false
  later_ne.ne _ _ _ h m hle r := match m with | .zero => .rfl | .succ k => h (m := k) (by omega) r
  pure_intro h _ _ _ := h
  pure_elim' h n r hφ := h hφ n r trivial
  and_elim_l _ _ h := h.1
  and_elim_r _ _ h := h.2
  and_intro h₁ h₂ n r h := ⟨h₁ n r h, h₂ n r h⟩
  or_intro_l _ _ h := .inl h
  or_intro_r _ _ h := .inr h
  or_elim h₁ h₂ n r h := h.elim (h₁ n r) (h₂ n r)
  imp_intro {P _ _} h n r hP m hm hQ := h m r ⟨P.closed hP hm, hQ⟩
  imp_elim h n r hPQ := h n r hPQ.1 n (Nat.le_refl n) hPQ.2
  sForall_intro h n r hP p hΨ := h p hΨ n r hP
  sForall_elim h n r hF := hF _ h
  sExists_intro h n r hP := ⟨_, h, hP⟩
  sExists_elim h n r := fun ⟨_, hΨ, hP⟩ => h _ hΨ n r hP
  sep_mono h₁ h₂ n r := fun ⟨r1, r2, e, a, b⟩ => ⟨r1, r2, e, h₁ n r1 a, h₂ n r2 b⟩
  emp_sep {P} := ⟨fun n r ⟨r1, r2, e, he, hp⟩ => by
      rcases e with e | e
      · subst e; exact P.ne0 hp
      · rcases he with he | he
        · subst he; exact P.ne0 hp
        · subst he; simp only [Bool.false_or] at e; subst e; exact hp,
    fun n r hp => ⟨false, r, .inr (by cases r <;> rfl), .inr rfl, hp⟩⟩
  sep_symm n r := fun ⟨r1, r2, e, a, b⟩ => ⟨r2, r1, e.imp_right (fun e => e.trans (Bool.or_comm _ _)), b, a⟩
  sep_assoc_l n r := fun ⟨r12, r3, e, ⟨r1, r2, e', a, b⟩, c⟩ => ⟨r1, or r2 r3, by
      rcases e with e | e
      · exact .inl e
      · rcases e' with e' | e'
        · exact .inl e'
        · exact .inr (by rw [e, e', Bool.or_assoc]), a, ⟨r2, r3, .inr rfl, b, c⟩⟩
  wand_intro {P Q R} h n r hP m hm r' hQ := h m (or r r') ⟨r, r', .inr rfl, P.closed hP hm, hQ⟩
  wand_elim {P Q R} h n r := fun ⟨r1, r2, e, a, b⟩ => by
    have := h n r1 a n (Nat.le_refl n) r2 b
    rcases e with e | e
    · subst e; exact R.ne0 this
    · rw [e]; exact this
  persistently_mono h n r hp := h n false hp
  persistently_idem_2 _ _ h := h
  persistently_emp_2 n r _ := .inr rfl
  persistently_and_2 _ _ h := h
  persistently_absorb_l n r := fun ⟨r1, r2, e, a, b⟩ => a
  persistently_and_l {P Q} n r h := ⟨false, r, .inr (by cases r <;> rfl), h.1, h.2⟩
  later_mono h n r hlP := match n with | .zero => trivial | .succ k => h k r hlP
  later_intro {P} n r hP := match n with | .zero => trivial | .succ _ => P.closed hP (by omega)
  later_sForall_2 n r h := match n with
    | .zero => trivial
    | .succ k => fun p hΦ => h _ ⟨p, rfl⟩ (k+1) (Nat.le_refl _) hΦ
  later_sExists_false {Φ} n r h := by
    cases n with
    | zero => exact .inl trivial
    | succ n =>
      obtain ⟨P, hΦP, hPn⟩ := h
      exact .inr ⟨_, ⟨P, rfl⟩, hΦP, hPn⟩
  later_sep {P Q} := ⟨fun n r h => match n with
      | .zero => ⟨r, false, .inl rfl, trivial, trivial⟩
      | .succ k => by
        obtain ⟨r1, r2, e, a, b⟩ := h
        rcases e with e | e
        · subst e; exact ⟨r, false, .inr (by cases r <;> rfl), P.ne0 a, Q.ne0 b⟩
        · exact ⟨r1, r2, .inr e, a, b⟩,
    fun n r h => match n with
      | .zero => trivial
      | .succ k => by
        obtain ⟨s1, s2, e, a, b⟩ := h
        exact ⟨s1, s2, .inr (e.resolve_left (by omega)), a, b⟩⟩
  later_persistently := ⟨fun n r h => match n with | 0 => trivial | _+1 => h,
    fun n r h => match n with | 0 => trivial | _+1 => h⟩
  later_false_em {P} n r hP := match n with
    | .zero => .inl trivial
    | .succ n => .inr fun m hle hF => match m with
      | .zero => P.closed hP (Nat.zero_le _)
      | .succ _ => absurd hF id

-- helper: in TP, emp is not timeless (later emp holds at step 1 at resource true, emp does not)
theorem tp_emp_not_timeless (h : (iprop(▷ emp) : TP) ⊢ iprop(◇ emp)) : False := by
  have := h 1 true (.inl rfl)
  rcases this with h1 | h1
  · exact h1
  · rcases h1 with h1 | h1 <;> simp at h1
-- helper
theorem tpT {Q : TP} (e : Q ⊣⊢ emp) (h : ▷ Q ⊢ ◇ Q) : False :=
  tp_emp_not_timeless ((later_mono e.2).trans (h.trans (except0_mono e.1)))
-- helper
instance tpTrue : Timeless (iprop(True) : TP) := ⟨(pure_intro trivial).trans except0_intro⟩

-- `Iris.BI.BigSepM.bigSepM_nil_timeless_inst` idx 6: necessary (TP, a step-indexed BI where emp holds at step 0 everywhere but not later: emp is not timeless; m empty)
theorem w4c2_137 : ¬ drop0% Iris.BI.BigSepM.bigSepM_nil_timeless_inst 6 := fun h =>
  tpT (BiEntails.of_eq (emE _)) (h (PROP := TP) (M := TM) (K := Nat) (V := Unit) (Φ := fun _ _ => iprop(True))).timeless

-- `Iris.BI.BigSepM.bigSepM_timeless` idx 6: necessary (TP, a BI where emp is not timeless; m empty)
theorem w4c2_138 : ¬ drop0% Iris.BI.BigSepM.bigSepM_timeless 6 := fun h =>
  tpT (BiEntails.of_eq (emE _)) (h (PROP := TP) (M := TM) (K := Nat) (V := Unit) (Φ := fun _ _ => iprop(True)) (m := ∅)
    (fun hk => by rw [get?_empty] at hk; cases hk)).timeless

-- `Iris.BI.BigSepM.bigSepM_timeless_inst` idx 6: necessary (TP, a BI where emp is not timeless; m empty, Phi = True)
theorem w4c2_139 : ¬ drop0% Iris.BI.BigSepM.bigSepM_timeless_inst 6 := fun h =>
  tpT (BiEntails.of_eq (emE _)) (h (PROP := TP) (M := TM) (K := Nat) (V := Unit) (Φ := fun _ _ => iprop(True)) (m := ∅)).timeless

-- `Iris.BI.BigSepM2.bigSepM2_timeless` idx 7: necessary (TP, a BI where emp is not timeless; maps empty)
theorem w4c2_140 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_timeless 7 := fun h =>
  tpT (BigSepM2.bigSepM2_empty _) (h (PROP := TP) (M := TM) (K := Nat) (A := Unit) (B := Unit) (fun _ _ _ => iprop(True)) ∅ ∅
    (fun h1 _ => by rw [get?_empty] at h1; cases h1)).timeless

-- `Iris.BI.BigSepM2.bigSepM2_empty_timeless_inst` idx 7: necessary (TP, a BI where emp is not timeless; maps empty)
theorem w4c2_141 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_empty_timeless_inst 7 := fun h =>
  tpT (BigSepM2.bigSepM2_empty _) (h (PROP := TP) (M := TM) (K := Nat) (A := Unit) (B := Unit) (fun _ _ _ => iprop(True))).timeless

-- `Iris.BI.BigSepM2.bigSepM2_timeless_inst` idx 7: necessary (TP, a BI where emp is not timeless; maps empty, Phi = True)
theorem w4c2_142 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_timeless_inst 7 := fun h =>
  tpT (BigSepM2.bigSepM2_empty _) (h (PROP := TP) (M := TM) (K := Nat) (A := Unit) (B := Unit) (Φ := fun _ _ _ => iprop(True))
    (m1 := ∅) (m2 := ∅)).timeless

-- `Iris.BI.BigSepM2.bigSepM2_later_1` idx 7: necessary (TP, a non-affine BI where emp is not timeless: maps empty, later emp does not entail except-0 emp)
theorem w4c2_143 : ¬ drop0% Iris.BI.BigSepM2.bigSepM2_later_1 7 := fun h =>
  tp_emp_not_timeless ((later_mono (BigSepM2.bigSepM2_empty _).2).trans
    ((h (PROP := TP) (M := TM) (K := Nat) (A := Unit) (B := Unit) (Φ := fun _ _ _ => iprop(True)) (m1 := ∅) (m2 := ∅)).trans
      (except0_mono (BigSepM2.bigSepM2_empty _).1)))

-- `Iris.BI.BigSepS.bigSepS_empty_timeless_inst` idx 5: necessary (TP, a BI where emp is not timeless; X empty)
theorem w4c2_144 : ¬ drop0% Iris.BI.BigSepS.bigSepS_empty_timeless_inst 5 := fun h =>
  tpT (seE _) (h (PROP := TP) (S := TS) (A := Nat) (Φ := fun _ => iprop(True))).timeless

-- `Iris.BI.BigSepS.bigSepS_timeless` idx 5: necessary (TP, a BI where emp is not timeless; X empty)
theorem w4c2_145 : ¬ drop0% Iris.BI.BigSepS.bigSepS_timeless 5 := fun h =>
  tpT (seE _) (h (PROP := TP) (S := TS) (A := Nat) (Φ := fun _ => iprop(True)) (X := ∅)
    (fun hx => (LawfulSet.mem_empty hx).elim)).timeless

-- `Iris.BI.BigSepS.bigSepS_timeless_inst` idx 5: necessary (TP, a BI where emp is not timeless; X empty, Phi = True)
theorem w4c2_146 : ¬ drop0% Iris.BI.BigSepS.bigSepS_timeless_inst 5 := fun h =>
  tpT (seE _) (h (PROP := TP) (S := TS) (A := Nat) (Φ := fun _ => iprop(True)) (X := ∅)).timeless

end W4c2
