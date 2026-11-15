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

namespace T3c6
open Iris Iris.BI Iris.Std

/-! ### D1: `[IncOrd M]` removable. Astra's witness: the whole left side `W := A ∗ vs₁₂ A Q`. -/

-- `Iris.fupd_vs_trans` idx 3: removable
theorem t3c6_0 : drop% Iris.fupd_vs_trans 3 := by
  intro M _ vs E1 E2 E3 P hpers vs_trans vs_exists vs_persistent_intro_r vs_impl
  have self : ∀ (E E' : CoPset) (A B : UPred M),
      (emp : UPred M) ⊢ vs E E' iprop(A ∗ vs E E' A B) B := fun E E' A B =>
    (wand_intro emp_sep.1).trans (@vs_persistent_intro_r E E' A B (vs E E' A B) hpers)
  have K : (emp : UPred M) ⊢ vs E2 E3 (fupd_vs vs E2 E3 P) P :=
    (forall_intro fun A => self E2 E3 A P).trans (vs_exists E2 E3 (fun A => iprop(A ∗ vs E2 E3 A P)) P)
  refine exists_elim fun A => ?_
  have h13 : (emp : UPred M) ⊢ vs E1 E3 iprop(A ∗ vs E1 E2 A (fupd_vs vs E2 E3 P)) P :=
    (and_intro (self E1 E2 A _) K).trans (vs_trans _ _ _ _ _ _)
  exact sep_emp.2.trans ((sep_mono_right h13).trans
    (exists_intro (Ψ := fun X => iprop(X ∗ vs E1 E3 X P)) _))

/-! ### D4: one-element algebra, `vs A B := ▷(A → B)`, so `fupd P = ▷P` -/

inductive O1 | e deriving DecidableEq

instance : OFE O1 := OFE.ofDiscrete O1
instance : OFE.Discrete O1 := ⟨id⟩

instance instORAO1 : ORA O1 := ORA.ofDiscreteORAData {
  pcore := fun _ => some .e
  op := fun _ _ => .e
  Valid := fun _ => True
  Order := fun _ _ => True
  assoc := by intro x y z; rfl
  comm := by intro x y; rfl
  pcore_op_left := by intro x cx h; cases h; cases x; rfl
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := fun _ _ _ => trivial
  ord_trans := fun _ _ _ _ _ => trivial
  op_mono_left := fun _ _ _ _ => trivial
  valid_of_ord := fun _ _ _ _ => trivial
  pcore_mono := by intro x y cx h1 h2; exact ⟨.e, rfl, trivial⟩
  pcore_order_op := by intro x cx h y; exact ⟨.e, rfl, trivial⟩
  pcore_increasing := fun _ _ _ _ => trivial
  increasing_closed := fun _ _ _ _ _ => trivial }

instance : OrderRefl O1 := ⟨fun _ => trivial⟩

instance instUORAO1 : UORA O1 where
  unit := .e
  unit_valid := trivial
  unit_left_id := fun {x} => by cases x; rfl
  pcore_unit := rfl

instance : IncOrd O1 := ⟨fun _ => trivial⟩

theorem allx (X : UPred O1) {n : Nat} {x y : ValidAt O1 n} (h : X n x) : X n y :=
  X.mono h trivial (Nat.le_refl n)

noncomputable def vs4 : CoPset → CoPset → UPred O1 → UPred O1 → UPred O1 :=
  fun _ _ A B => iprop(▷ (A → B))

instance pers4 (X : UPred O1) : Persistent X := ⟨fun _ _ h => allx X h⟩

theorem trans4 (A B C : UPred O1) : iprop(▷ (A → B) ∧ ▷ (B → C)) ⊢ iprop(▷ (A → C)) := by
  rintro (_ | n) x ⟨h1, h2⟩
  · trivial
  · exact fun x' hx hn hA => h2 x' hx hn (h1 x' hx hn hA)

theorem exists4 {α : Type} (Φ : α → UPred O1) (Q : UPred O1) :
    iprop(∀ i, ▷ (Φ i → Q)) ⊢ iprop(▷ ((∃ i, Φ i) → Q)) := by
  rintro (_ | n) x h
  · trivial
  · intro n' x' hx hn hE
    obtain ⟨_, ⟨i, rfl⟩, hΦ⟩ := hE
    exact h _ ⟨i, rfl⟩ x' hx hn hΦ

theorem impl4 (A B : UPred O1) : iprop(□ (A → B)) ⊢ iprop(▷ (A → B)) :=
  intuitionistically_elim.trans later_intro

theorem lhs4 : fupd_vs vs4 ∅ ∅ (fupd_vs vs4 ∅ ∅ iprop(False)) 1 ⟨.e, trivial⟩ :=
  ⟨_, ⟨iprop(True), rfl⟩, .e, .e, trivial, trivial, fun {n'} x' _ hn _ => by
    rcases n' with _ | k
    · exact ⟨_, ⟨iprop(True), rfl⟩, .e, .e, trivial, trivial, trivial⟩
    · exact absurd hn (Nat.not_succ_le_zero k)⟩

theorem rhs4 : ¬ fupd_vs vs4 ∅ ∅ iprop(False) 1 ⟨.e, trivial⟩ := by
  rintro ⟨_, ⟨R, rfl⟩, x1, x2, _, hR, hvs⟩
  exact hvs ⟨x1, trivial⟩ trivial (Nat.le_refl 0) (R.mono hR trivial (Nat.zero_le 1))

-- `Iris.fupd_vs_trans` idx 11: necessary
theorem t3c6_3 : ¬ drop0% Iris.fupd_vs_trans 11 := fun h =>
  rhs4 (@h O1 _ vs4 inferInstance ∅ ∅ ∅ iprop(False) (fun {_ _ _ _} => pers4 _)
    (fun _ _ _ A B C => trans4 A B C) (fun {_} _ _ Φ Q => exists4 Φ Q) (fun _ A B => impl4 A B)
    1 ⟨.e, trivial⟩ lhs4)

/-! ### D2/D3: subsets of {a,b} under union, ordered by ⊆, core = ∅ (affine, IncOrd) -/

inductive F4 | e | a | b | t deriving DecidableEq

def F4.op : F4 → F4 → F4
  | .e, y => y
  | x, .e => x
  | .a, .a => .a
  | .b, .b => .b
  | _, _ => .t

def F4.leb : F4 → F4 → Bool
  | .e, _ => true
  | .a, .a => true
  | .a, .t => true
  | .b, .b => true
  | .b, .t => true
  | .t, .t => true
  | _, _ => false

instance : OFE F4 := OFE.ofDiscrete F4
instance : OFE.Discrete F4 := ⟨id⟩

instance instORAF4 : ORA F4 := ORA.ofDiscreteORAData {
  pcore := fun _ => some .e
  op := F4.op
  Valid := fun _ => True
  Order := fun x y => F4.leb x y = true
  assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  comm := by intro x y; cases x <;> cases y <;> rfl
  pcore_op_left := by intro x cx h; cases h; cases x <;> rfl
  pcore_idem := by intro x cx h; cases h; rfl
  valid_op_left := fun _ _ _ => trivial
  ord_trans := by intro x y z h1 h2; revert h1 h2; cases x <;> cases y <;> cases z <;> decide
  op_mono_left := by intro x y z h; revert h; cases x <;> cases y <;> cases z <;> decide
  valid_of_ord := fun _ _ _ _ => trivial
  pcore_mono := by intro x y cx h1 h2; exact ⟨.e, rfl, by cases h2; rfl⟩
  pcore_order_op := by intro x cx h y; exact ⟨.e, rfl, by cases h; rfl⟩
  pcore_increasing := by intro x cx h y; cases h; cases y <;> rfl
  increasing_closed := by intro x y _ _ z; cases y <;> cases z <;> rfl }

instance : OrderRefl F4 := ⟨fun x => by cases x <;> rfl⟩

instance instUORAF4 : UORA F4 where
  unit := .e
  unit_valid := trivial
  unit_left_id := rfl
  pcore_unit := rfl

instance : IncOrd F4 := ⟨by
  intro x y ⟨z, hz⟩
  show F4.leb x y = true
  cases x <;> cases z <;> simp_all [Op.op, F4.op, F4.leb] <;> cases y <;> simp_all [F4.leb]⟩

theorem leb_trans {x y z : F4} (h1 : F4.leb x y = true) (h2 : F4.leb y z = true) : F4.leb x z = true := by
  revert h1 h2; cases x <;> cases y <;> cases z <;> decide
theorem le_op_left (x y : F4) : F4.leb x (F4.op x y) = true := by cases x <;> cases y <;> rfl
theorem op_e (x : F4) : F4.op x .e = x := by cases x <;> rfl

abbrev up (P : UPred F4) (m : Nat) (z : F4) : Prop := P m ⟨z, trivial⟩

/-- the left factor of a split lies below the whole -/
theorem sep_left {P T : UPred F4} {m : Nat} {z : F4} (h : up iprop(P ∗ T) m z) : up P m z := by
  obtain ⟨x1, x2, H, hP, _⟩ := h
  exact P.mono hP (leb_trans (le_op_left x1 x2) H) (Nat.le_refl m)

/-- a persistent proposition true somewhere at step m is true at the unit -/
theorem pers_e {T : UPred F4} [Persistent T] {m : Nat} {z : F4} (h : up T m z) : up T m .e :=
  (Persistent.persistent : T ⊢ iprop(<pers> T)) m ⟨z, trivial⟩ h

theorem sep_right_e {P T : UPred F4} [Persistent T] {m : Nat} {z : F4} (h : up iprop(P ∗ T) m z) :
    up T m .e := by
  obtain ⟨x1, x2, H, _, hT⟩ := h
  exact pers_e hT

/-! #### D3: mask- and resource-independent `vs`; the preorder ρ is not closed under binary unions -/

def inA (z : F4) : Prop := z = .a ∨ z = .t
def inB (z : F4) : Prop := z = .b ∨ z = .t

/-- reflexive-transitive closure of ⊆, A → ∅, B → ∅, M → C, in closed form -/
def rho3 (X Y : F4 → Prop) : Prop :=
  (∀ z, X z → Y z) ∨ (∀ z, X z → inA z) ∨ (∀ z, X z → inB z) ∨ (Y .a ∧ Y .b ∧ Y .t)

theorem rho3_trans {X Y Z : F4 → Prop} (h1 : rho3 X Y) (h2 : rho3 Y Z) : rho3 X Z := by
  rcases h1 with h1 | h1 | h1 | h1
  · rcases h2 with h2 | h2 | h2 | h2
    · exact .inl fun z hz => h2 z (h1 z hz)
    · exact .inr (.inl fun z hz => h2 z (h1 z hz))
    · exact .inr (.inr (.inl fun z hz => h2 z (h1 z hz)))
    · exact .inr (.inr (.inr h2))
  · exact .inr (.inl h1)
  · exact .inr (.inr (.inl h1))
  · rcases h2 with h2 | h2 | h2 | h2
    · exact .inr (.inr (.inr ⟨h2 _ h1.1, h2 _ h1.2.1, h2 _ h1.2.2⟩))
    · rcases h2 _ h1.2.1 with h | h <;> cases h
    · rcases h2 _ h1.1 with h | h <;> cases h
    · exact .inr (.inr (.inr h2))

theorem rho3_left {X X' Y : F4 → Prop} (h : rho3 X Y) (hs : ∀ z, X' z → X z) : rho3 X' Y := by
  rcases h with h | h | h | h
  · exact .inl fun z hz => h z (hs z hz)
  · exact .inr (.inl fun z hz => h z (hs z hz))
  · exact .inr (.inr (.inl fun z hz => h z (hs z hz)))
  · exact .inr (.inr (.inr h))

def V3 (P Q : UPred F4) : UPred F4 where
  holds n _ := ∀ m, m ≤ n → rho3 (up P m) (up Q m)
  mono h _ hn m hm := h m (Nat.le_trans hm hn)

def vs3 : CoPset → CoPset → UPred F4 → UPred F4 → UPred F4 := fun _ _ => V3

instance pers3 (P Q : UPred F4) : Persistent (V3 P Q) := ⟨fun _ _ h => h⟩

theorem trans3 (P Q R : UPred F4) : iprop(V3 P Q ∧ V3 Q R) ⊢ V3 P R :=
  fun _ _ ⟨h1, h2⟩ m hm => rho3_trans (h1 m hm) (h2 m hm)

theorem pir3 (P Q T : UPred F4) [Persistent T] : iprop(T -∗ V3 P Q) ⊢ V3 iprop(P ∗ T) Q := by
  intro n x h m hm
  by_cases hT : up T m .e
  · exact rho3_left (h m .e hm trivial hT m (Nat.le_refl m)) fun z hz => sep_left hz
  · exact .inl fun z hz => absurd (sep_right_e hz) hT

theorem impl3 (P Q : UPred F4) : iprop(□ (P → Q)) ⊢ V3 P Q := by
  rintro n x ⟨_, h⟩ m hm
  exact .inl fun z hz => h ⟨z, trivial⟩ rfl hm hz

abbrev fu3 (X : UPred F4) : UPred F4 := fupd_vs vs3 ∅ ∅ X

theorem fF3a (m : Nat) (z : F4) (hz : inA z) : up (fu3 iprop(False)) m z := by
  refine ⟨_, ⟨UPred.ownM F4.a, rfl⟩, .a, .e, ?_, rfl, fun k _ => .inr (.inl fun w hw => ?_)⟩
  · show F4.leb (F4.op .a .e) z = true
    rcases hz with rfl | rfl <;> rfl
  · have hw' : F4.leb .a w = true := hw
    cases w <;> simp_all [inA, F4.leb]

theorem fF3b (m : Nat) (z : F4) (hz : inB z) : up (fu3 iprop(False)) m z := by
  refine ⟨_, ⟨UPred.ownM F4.b, rfl⟩, .b, .e, ?_, rfl, fun k _ => .inr (.inr (.inl fun w hw => ?_))⟩
  · show F4.leb (F4.op .b .e) z = true
    rcases hz with rfl | rfl <;> rfl
  · have hw' : F4.leb .b w = true := hw
    cases w <;> simp_all [inB, F4.leb]

theorem lhs3 : fu3 (fu3 iprop(False)) 0 ⟨.e, trivial⟩ :=
  ⟨_, ⟨iprop(True), rfl⟩, .e, .e, rfl, trivial, fun m _ =>
    .inr (.inr (.inr ⟨fF3a m .a (.inl rfl), fF3b m .b (.inl rfl), fF3a m .t (.inr rfl)⟩))⟩

theorem rhs3 : ¬ fu3 iprop(False) 0 ⟨.e, trivial⟩ := by
  rintro ⟨_, ⟨R, rfl⟩, x1, x2, H, hR, hV⟩
  have H' : F4.leb (F4.op x1 x2) .e = true := H
  have h0 : rho3 (up R 0) (up iprop(False) 0) := hV 0 (Nat.le_refl 0)
  cases x1 <;> cases x2 <;> simp [F4.op, F4.leb] at H'
  rcases h0 with h | h | h | h
  · exact h _ hR
  · rcases h _ hR with h | h <;> cases h
  · rcases h _ hR with h | h <;> cases h
  · exact h.1

-- `Iris.fupd_vs_trans` idx 10: necessary
theorem t3c6_2 : ¬ drop0% Iris.fupd_vs_trans 10 := fun h =>
  rhs3 (@h F4 _ vs3 inferInstance ∅ ∅ ∅ iprop(False) (fun {_ _ _ _} => pers3 _ _)
    (fun _ _ _ P Q R => trans3 P Q R) (fun _ _ P Q R inst => @pir3 P Q R inst)
    (fun _ P Q => impl3 P Q) 0 ⟨.e, trivial⟩ lhs3)

/-! #### D2: the same algebra, a resource-dependent (non-persistent) `vs` -/

def rho2 : F4 → (F4 → Prop) → (F4 → Prop) → Prop
  | .e, X, Y => ∀ z, X z → Y z
  | .b, X, Y => (∀ z, X z → Y z) ∨ (Y .a ∧ Y .t)
  | _, _, _ => True

theorem rho2_sub {x : F4} {X Y : F4 → Prop} (h : ∀ z, X z → Y z) : rho2 x X Y := by
  cases x
  · exact h
  · trivial
  · exact .inl h
  · trivial

theorem rho2_mono {x y : F4} {X Y : F4 → Prop} (hxy : F4.leb x y = true) (h : rho2 x X Y) : rho2 y X Y := by
  cases x <;> cases y <;> simp [F4.leb] at hxy
  all_goals first | exact h | exact rho2_sub h | trivial

theorem rho2_trans {x : F4} {X Y Z : F4 → Prop} (h1 : rho2 x X Y) (h2 : rho2 x Y Z) : rho2 x X Z := by
  cases x
  · exact fun z hz => h2 z (h1 z hz)
  · trivial
  · rcases h2 with h2 | h2
    · rcases h1 with h1 | h1
      · exact .inl fun z hz => h2 z (h1 z hz)
      · exact .inr ⟨h2 _ h1.1, h2 _ h1.2⟩
    · exact .inr h2
  · trivial

theorem rho2_left {x : F4} {X X' Y : F4 → Prop} (h : rho2 x X Y) (hs : ∀ z, X' z → X z) : rho2 x X' Y := by
  cases x
  · exact fun z hz => h z (hs z hz)
  · trivial
  · rcases h with h | h
    · exact .inl fun z hz => h z (hs z hz)
    · exact .inr h
  · trivial

def V2 (P Q : UPred F4) : UPred F4 where
  holds n x := ∀ m, m ≤ n → rho2 x.val (up P m) (up Q m)
  mono h hle hn m hm := rho2_mono hle (h m (Nat.le_trans hm hn))

def vs2 : CoPset → CoPset → UPred F4 → UPred F4 → UPred F4 := fun _ _ => V2

theorem trans2 (P Q R : UPred F4) : iprop(V2 P Q ∧ V2 Q R) ⊢ V2 P R :=
  fun _ _ ⟨h1, h2⟩ m hm => rho2_trans (h1 m hm) (h2 m hm)

theorem exists2 {α : Type} (Φ : α → UPred F4) (Q : UPred F4) :
    iprop(∀ i, V2 (Φ i) Q) ⊢ V2 iprop(∃ i, Φ i) Q := by
  intro n x h m hm
  have hi : ∀ i, rho2 x.val (up (Φ i) m) (up Q m) := fun i => h _ ⟨i, rfl⟩ m hm
  rcases x with ⟨x, hx⟩
  cases x
  · intro z hz
    obtain ⟨_, ⟨i, rfl⟩, hz⟩ := hz
    exact hi i z hz
  · trivial
  · by_cases hc : up Q m .a ∧ up Q m .t
    · exact .inr hc
    · refine .inl fun z hz => ?_
      obtain ⟨_, ⟨i, rfl⟩, hz⟩ := hz
      rcases hi i with h' | h'
      · exact h' z hz
      · exact absurd h' hc
  · trivial

theorem pir2 (P Q T : UPred F4) [Persistent T] : iprop(T -∗ V2 P Q) ⊢ V2 iprop(P ∗ T) Q := by
  intro n x h m hm
  by_cases hT : up T m .e
  · have hv : rho2 (F4.op x.val .e) (up P m) (up Q m) := h m .e hm trivial hT m (Nat.le_refl m)
    rw [op_e] at hv
    exact rho2_left hv fun z hz => sep_left hz
  · exact rho2_sub fun z hz => absurd (sep_right_e hz) hT

theorem impl2 (P Q : UPred F4) : iprop(□ (P → Q)) ⊢ V2 P Q := by
  rintro n x ⟨_, h⟩ m hm
  exact rho2_sub fun z hz => h ⟨z, trivial⟩ rfl hm hz

abbrev fu2 (X : UPred F4) : UPred F4 := fupd_vs vs2 ∅ ∅ X

theorem fF2 (m : Nat) (z : F4) (hz : inA z) : up (fu2 iprop(False)) m z := by
  rcases hz with rfl | rfl
  · exact ⟨_, ⟨iprop(True), rfl⟩, .e, .a, rfl, trivial, fun _ _ => trivial⟩
  · exact ⟨_, ⟨iprop(True), rfl⟩, .e, .t, rfl, trivial, fun _ _ => trivial⟩

theorem lhs2 : fu2 (fu2 iprop(False)) 0 ⟨.b, trivial⟩ :=
  ⟨_, ⟨iprop(True), rfl⟩, .e, .b, rfl, trivial, fun m _ => .inr ⟨fF2 m .a (.inl rfl), fF2 m .t (.inr rfl)⟩⟩

theorem rhs2 : ¬ fu2 iprop(False) 0 ⟨.b, trivial⟩ := by
  rintro ⟨_, ⟨R, rfl⟩, x1, x2, H, hR, hV⟩
  have H' : F4.leb (F4.op x1 x2) .b = true := H
  have h0 : rho2 x2 (up R 0) (up iprop(False) 0) := hV 0 (Nat.le_refl 0)
  cases x1 <;> cases x2 <;> simp [F4.op, F4.leb] at H'
  all_goals first
    | exact h0 _ hR
    | (rcases h0 with h0 | h0
       · exact h0 _ hR
       · exact h0.1)

-- `Iris.fupd_vs_trans` idx 8: necessary
theorem t3c6_1 : ¬ drop0% Iris.fupd_vs_trans 8 := fun h =>
  rhs2 (@h F4 _ vs2 inferInstance ∅ ∅ ∅ iprop(False)
    (fun _ _ _ P Q R => trans2 P Q R) (fun {_} _ _ Φ Q => exists2 Φ Q)
    (fun _ _ P Q R inst => @pir2 P Q R inst) (fun _ P Q => impl2 P Q) 0 ⟨.b, trivial⟩ lhs2)

end T3c6
