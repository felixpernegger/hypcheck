import Std
import Lean

/-!
Hand pass `Order` (hand15): the 161 unresolved hypotheses of `Std.Internal.Order.*` (`Heyting`,
`Lemmas`, `FrameClosure`, `OfProp`, `PreservesSup`, `Basic`, `Product`, `Prop`, `PredTrans`).
150 necessary (6 of them dependent), 11 removable, 0 independent.

Reusable models (namespace `OrderHand`, copy what you need):
* `Prop` with the scoped `Std.Internal.Order` lattice; tactic `prop_simp` rewrites `⊑ ⊓ ⊔ ⊤ ⊥ ⇨ ⌜·⌝`
  to `→ ∧ ∨ True False → ·` (`clear` the refuted hypothesis first, `simp_all` would use it).
* `not_ps_true`: the constant `True` map on `Prop` does not preserve suprema; `ps_false`: the
  constant `False` map does; `not_ps_of f z`: no value of f below z refutes `PreservesSup f`
  (via `ps_sup_empty_le`: a supremum-preserving map sends `sup ∅` below everything).
* `M3` (`o < x, y, z < i`, the non-distributive diamond): a computable `CompleteLattice` with
  decidable `⊑`, tables `M3.meet_eq`, `M3.join_eq`, `M3.himp_eq` (`a ⇨ b = i` unless `a = i`),
  `M3.top_eq`, `M3.bot_eq`; tactic `m3_dec` rewrites with them and decides. `M3.not_ps_x`: meeting
  with an atom does not preserve suprema, so `M3` is no frame (`Heyting` fails).
* `not_ps_meet a b c q r`: generic refutation of `PreservesSup (meet a)` from order facts only;
  lifts the M3 failure to `PProd`/`Prod`/function lattices over M3.
* `sw` (swap on `Bool → Prop`, `ps_sw` by `ps_of_iso`): a supremum-preserving map with
  `sw ∘ sw ≠ sw`, used against the action laws of `PredTrans.frameClosure_frames`.
* `mkFO op opE h1 h2`: a `FrameOp` instance from its two `PreservesSup` facts; `fc_le`: upper bound
  of a frame closure through one resource.

Removable (11): `⇨` is antitone/monotone and `⊤ ⇨ P = P`, `⌜φ₁⌝ ⇨ ⌜φ₂⌝ = ⌜φ₁ → φ₂⌝` in every
complete lattice (no `Heyting`); `upperAdjoint f` is monotone for any f; the `fst` (`snd`)
component of the upper adjoint of a product map needs only that the other component map preserves
suprema (it then sends `⊥` to `⊥`).

Run with the lean4 repo's stage1 binary: `runs/hand15/lean.sh checks/OrderHand.lean`.
-/

set_option linter.unusedVariables false

open Lean Meta Elab Term in
/-- `drop% T i`: `T` with its (non-dependent) Prop binder `i` dropped, read off the library. -/
elab "drop% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

open Lean Meta Elab Term in
/-- `indep% T i`: `∀ indep, Hᵢ` for the dependent Prop binder `i` of `T` (all independent binders). -/
elab "indep% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    let mut dep := #[x]
    for j in [i.getNat+1:xs.size] do
      let t ← inferType xs[j]!
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push xs[j]!
    unless dep.size > 1 || body.containsFVar x.fvarId! do
      throwError "binder {i.getNat} of {n} is not dependent"
    mkForallFVars (xs.filter (fun y => !dep.contains y)) (← inferType x)

open Lean Meta Elab Term in
/-- `drop0% T i`: `drop% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "drop0% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.zero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

open Lean Meta Elab Term in
/-- `indep0% T i`: `indep% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "indep0% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.zero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    let mut dep := #[x]
    for j in [i.getNat+1:xs.size] do
      let t ← inferType xs[j]!
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push xs[j]!
    unless dep.size > 1 || body.containsFVar x.fvarId! do
      throwError "binder {i.getNat} of {n} is not dependent"
    mkForallFVars (xs.filter (fun y => !dep.contains y)) (← inferType x)


open Lean.Order Std.Internal.Order PartialOrder

namespace OrderHand

universe u

section Generic
variable {L : Type u} [CompleteLattice L]

-- a supremum-preserving map sends the empty supremum below every element
theorem ps_sup_empty_le (f : L → L) [PreservesSup f] (z : L) :
    f (CompleteLattice.sup (fun _ => False)) ⊑ z := by
  rw [PreservesSup.map_sup (f := f)]
  exact sup_le _ (fun _ ⟨_, h, _⟩ => h.elim)

-- a map none of whose values lies below z does not preserve suprema
theorem not_ps_of (f : L → L) (z : L) (h : ∀ x, ¬ f x ⊑ z) : ¬ PreservesSup f :=
  fun _ => h _ (ps_sup_empty_le f z)

-- the frame law fails at a: elements q, r whose meets with a lie below b, and c below a and
-- below every upper bound of q and r, but not below b
theorem not_ps_meet (a b c q r : L)
    (h1 : ∀ w, w ⊑ a → w ⊑ q → w ⊑ b) (h2 : ∀ w, w ⊑ a → w ⊑ r → w ⊑ b)
    (h3 : ∀ u, q ⊑ u → r ⊑ u → c ⊑ u) (h4 : c ⊑ a) (h5 : ¬ c ⊑ b) :
    ¬ PreservesSup (meet a) := by
  intro hps
  apply h5
  have hq : q ⊑ a ⇨ b := le_himp_of_meet_le_left (h1 _ (meet_le_left _ _) (meet_le_right _ _))
  have hr : r ⊑ a ⇨ b := le_himp_of_meet_le_left (h2 _ (meet_le_left _ _) (meet_le_right _ _))
  exact rel_trans (le_meet _ _ _ h4 (h3 _ hq hr)) meet_himp_le

theorem meet_eq_of {a b m : L} (h : ∀ w, w ⊑ m ↔ w ⊑ a ∧ w ⊑ b) : a ⊓ b = m :=
  rel_antisymm ((h _).2 ⟨meet_le_left _ _, meet_le_right _ _⟩)
    (le_meet _ _ _ ((h m).1 rel_refl).1 ((h m).1 rel_refl).2)

theorem join_eq_of {a b j : L} (h : ∀ w, j ⊑ w ↔ a ⊑ w ∧ b ⊑ w) : a ⊔ b = j :=
  rel_antisymm (join_le _ _ _ ((h j).1 rel_refl).1 ((h j).1 rel_refl).2)
    ((h _).2 ⟨left_le_join _ _, right_le_join _ _⟩)

theorem sup_eq_of {c : L → Prop} {s : L} (h : is_sup c s) : CompleteLattice.sup c = s :=
  is_sup_unique (CompleteLattice.sup_spec c) h

-- an order automorphism (with monotone inverse) preserves suprema
theorem ps_of_iso (f g : L → L) (hf : ∀ a b, a ⊑ b → f a ⊑ f b) (hg : ∀ a b, a ⊑ b → g a ⊑ g b)
    (hgf : ∀ a, g (f a) = a) (hfg : ∀ a, f (g a) = a) : PreservesSup f where
  map_sup s := by
    apply rel_antisymm
    · have : CompleteLattice.sup s ⊑ g (CompleteLattice.sup (fun y => ∃ x, s x ∧ y = f x)) :=
        sup_le _ fun x hx => by
          rw [← hgf x]; exact hg _ _ (le_sup _ ⟨x, hx, rfl⟩)
      have := hf _ _ this
      rwa [hfg] at this
    · exact sup_le _ fun _ ⟨x, hx, e⟩ => e ▸ hf _ _ (le_sup _ hx)

end Generic

/-! ## Prop -/

-- the constant `True` map on `Prop` does not preserve suprema (it sends `⊥` to `True`)
theorem not_ps_true : ¬ PreservesSup (fun _ : Prop => True) :=
  not_ps_of _ False fun _ h => h trivial

instance ps_false : PreservesSup (fun _ : Prop => False) where
  map_sup _ := propext ⟨False.elim, fun h =>
    (sup_le _ (fun _ ⟨_, _, e⟩ hy => by subst e; exact hy) : _ ⊑ False) h⟩

/-! ## The swap automorphism of `Bool → Prop` -/

def sw (P : Bool → Prop) : Bool → Prop := fun b => P (!b)

instance ps_sw : PreservesSup sw :=
  ps_of_iso sw sw (fun _ _ h b => h _) (fun _ _ h b => h _)
    (fun P => funext fun b => by simp [sw]) (fun P => funext fun b => by simp [sw])

/-! ## M3: the diamond with three atoms (not distributive, so no frame) -/

inductive M3 | o | x | y | z | i deriving DecidableEq

namespace M3

def leB : M3 → M3 → Bool
  | o, _ => true
  | _, i => true
  | x, x | y, y | z, z => true
  | _, _ => false

def meetF : M3 → M3 → M3
  | i, b => b
  | a, i => a
  | x, x => x
  | y, y => y
  | z, z => z
  | _, _ => o

def joinF : M3 → M3 → M3
  | o, b => b
  | a, o => a
  | x, x => x
  | y, y => y
  | z, z => z
  | _, _ => i

def himpF : M3 → M3 → M3
  | i, b => b
  | _, _ => i

def all : List M3 := [o, x, y, z, i]

theorem mem_all (a : M3) : a ∈ all := by cases a <;> decide

instance decForall (P : M3 → Prop) [DecidablePred P] : Decidable (∀ a, P a) :=
  decidable_of_iff (∀ a ∈ all, P a) ⟨fun h a => h a (mem_all a), fun h a _ => h a⟩

theorem leB_refl : ∀ a, leB a a = true := by decide
theorem leB_trans : ∀ a b c, leB a b = true → leB b c = true → leB a c = true := by decide
theorem leB_antisymm : ∀ a b, leB a b = true → leB b a = true → a = b := by decide
theorem joinF_le : ∀ a b u, leB (joinF a b) u = (leB a u && leB b u) := by decide
theorem le_meetF : ∀ a b w, leB w (meetF a b) = (leB w a && leB w b) := by decide
theorem himpF_spec : ∀ a b u,
    leB (himpF a b) u = true ↔ ∀ v, leB (meetF a v) b = true → leB v u = true := by decide

instance : PartialOrder M3 where
  rel a b := leB a b = true
  rel_refl := leB_refl _
  rel_trans := leB_trans _ _ _
  rel_antisymm := leB_antisymm _ _

instance (a b : M3) : Decidable (a ⊑ b) := inferInstanceAs (Decidable (leB a b = true))

theorem le_iff {a b : M3} : a ⊑ b ↔ leB a b = true := Iff.rfl

noncomputable def supL (c : M3 → Prop) : List M3 → M3
  | [] => o
  | a :: as => open Classical in if c a then joinF a (supL c as) else supL c as

theorem supL_le (c : M3 → Prop) (u : M3) :
    ∀ L : List M3, leB (supL c L) u = true ↔ ∀ v ∈ L, c v → leB v u = true
  | [] => by simp [supL, leB]
  | a :: as => by
    have ih := supL_le c u as
    by_cases h : c a <;> simp [supL, h, joinF_le, ih]

noncomputable instance : CompleteLattice M3 where
  has_sup c := ⟨supL c all, fun u => by
    show leB _ u = true ↔ _
    rw [supL_le]
    exact ⟨fun h v hv => h v (mem_all v) hv, fun h v _ hv => h v hv⟩⟩

theorem meet_eq (a b : M3) : a ⊓ b = meetF a b :=
  meet_eq_of fun w => by simp only [le_iff, le_meetF, Bool.and_eq_true]

theorem join_eq (a b : M3) : a ⊔ b = joinF a b :=
  join_eq_of fun w => by simp only [le_iff, joinF_le, Bool.and_eq_true]

theorem top_eq : (⊤ : M3) = i :=
  rel_antisymm (by show leB _ i = true; cases (⊤ : M3) <;> rfl) (le_top _)

theorem bot_eq : (⊥ : M3) = o := rel_antisymm (bot_le o) rfl

theorem himp_eq (a b : M3) : a ⇨ b = himpF a b := by
  unfold himp PreservesSup.upperAdjoint
  apply sup_eq_of
  intro u
  simp only [meet_eq]
  exact himpF_spec a b u

-- M3 is not a frame: meeting with an atom does not preserve suprema
theorem not_ps_x : ¬ PreservesSup (meet x) :=
  not_ps_meet x o x y z (by decide) (by decide) (by decide) rfl (by decide)

end M3

end OrderHand

/-! ## More helpers -/

namespace OrderHand

macro "prop_simp" : tactic => `(tactic| simp_all [le_prop_eq_imp, meet_prop_eq_and, join_prop_eq_or,
  top_prop_eq, bot_prop_eq, himp_prop_eq_imp, CompleteLattice.ofProp_prop_eq])

macro "m3_dec" : tactic => `(tactic| ((try simp only [M3.himp_eq, M3.meet_eq, M3.join_eq, M3.top_eq,
  M3.bot_eq]) <;> decide))

namespace M3
theorem lb_xy : ∀ w : M3, w ⊑ x → w ⊑ y → w ⊑ o := by decide
theorem lb_yx : ∀ w : M3, w ⊑ y → w ⊑ x → w ⊑ o := by decide
theorem lb_xz : ∀ w : M3, w ⊑ x → w ⊑ z → w ⊑ o := by decide
theorem ub_yz : ∀ u : M3, y ⊑ u → z ⊑ u → x ⊑ u := by decide
theorem ub_xy : ∀ u : M3, x ⊑ u → y ⊑ u → i ⊑ u := by decide
end M3

section Generic
universe v
variable {L : Type u} [CompleteLattice L]

theorem ua_le (f : L → L) (b y : L) (h : ∀ x, f x ⊑ b → x ⊑ y) :
    PreservesSup.upperAdjoint f b ⊑ y := sup_le _ h

theorem top_himp' (P : L) : (⊤ : L) ⇨ P = P :=
  rel_antisymm (sup_le _ fun x (hx : ⊤ ⊓ x ⊑ P) => by rw [top_meet] at hx; exact hx)
    (PreservesSup.le_upperAdjoint (meet ⊤) (meet_le_right _ _))

theorem bot_himp' (P : L) : (⊥ : L) ⇨ P = ⊤ :=
  rel_antisymm (le_top _)
    (PreservesSup.le_upperAdjoint (meet ⊥) (rel_trans (meet_le_left _ _) (bot_le _)))

theorem ofProp_himp' (φ₁ φ₂ : Prop) : ((⌜φ₁⌝ : L) ⇨ ⌜φ₂⌝) = ⌜φ₁ → φ₂⌝ := by
  by_cases h : φ₁
  · rw [CompleteLattice.ofProp_eq_top (l := L) h, top_himp']
    exact CompleteLattice.ofProp_congr ⟨fun h2 _ => h2, fun f => f h⟩
  · rw [CompleteLattice.ofProp_eq_top (l := L) (φ := φ₁ → φ₂) (fun h1 => absurd h1 h),
      show (⌜φ₁⌝ : L) = ⊥ by simp [CompleteLattice.ofProp, h], bot_himp']

theorem prodMap_fst' {β : Type v} [CompleteLattice β] (f : L → L) (g : β → β) [PreservesSup g]
    (E : L × β) :
    (PreservesSup.upperAdjoint (Prod.map f g) E).fst = PreservesSup.upperAdjoint f E.fst := by
  unfold PreservesSup.upperAdjoint
  rw [Prod.fst_sup]
  congr 1; funext a; apply propext
  exact ⟨fun ⟨_, h⟩ => h.1, fun h => ⟨_, h, ps_sup_empty_le g E.2⟩⟩

theorem prodMap_snd' {β : Type v} [CompleteLattice β] (f : L → L) (g : β → β) [PreservesSup f]
    (E : L × β) :
    (PreservesSup.upperAdjoint (Prod.map f g) E).snd = PreservesSup.upperAdjoint g E.snd := by
  unfold PreservesSup.upperAdjoint
  rw [Prod.snd_sup]
  congr 1; funext b; apply propext
  exact ⟨fun ⟨_, h⟩ => h.2, fun h => ⟨_, ps_sup_empty_le f E.1, h⟩⟩

end Generic

-- a frame operator from its two supremum-preservation facts
theorem mkFO {Pred : Type u} [CompleteLattice Pred] {R : Type} (op : R → Pred → Pred)
    {EPosts : Type} [CompleteLattice EPosts] (opE : R → EPosts → EPosts)
    (h1 : ∀ r, PreservesSup (op r)) (h2 : ∀ r, PreservesSup (opE r)) : FrameOp op EPosts opE :=
  { preservesSup := h1, preservesSupE := h2 }

theorem ps_id : PreservesSup (id : Prop → Prop) := inferInstance

theorem sw_mono {P Q : Bool → Prop} (h : P ⊑ Q) : sw P ⊑ sw Q := fun b => h (!b)

end OrderHand

namespace OrderHand

/-! ## Std.Internal.Order.Lemmas (model `Prop`) -/

-- `Lean.Order.le_meet`: in `Prop`, x = z = True, y = False.
theorem le_meet_5 : ¬ drop0% Lean.Order.le_meet 5 := fun H => by
  have h := H (α := Prop) True False True (fun _ => trivial); clear H; prop_simp

-- `Lean.Order.le_meet`: in `Prop`, x = y = True, z = False.
theorem le_meet_6 : ¬ drop0% Lean.Order.le_meet 6 := fun H => by
  have h := H (α := Prop) True True False (fun _ => trivial); clear H; prop_simp

-- `Lean.Order.join_le`: in `Prop`, x = True, y = z = False.
theorem join_le_5 : ¬ drop0% Lean.Order.join_le 5 := fun H => by
  have h := H (α := Prop) True False False id; clear H; prop_simp

-- `Lean.Order.join_le`: in `Prop`, y = True, x = z = False.
theorem join_le_6 : ¬ drop0% Lean.Order.join_le 6 := fun H => by
  have h := H (α := Prop) False True False id; clear H; prop_simp

-- `Lean.Order.le_iInf`: in `Prop`, f = const False over a one-point index, x = True.
theorem le_iInf_5 : ¬ drop0% Lean.Order.le_iInf 5 := fun H =>
  (iInf_le (fun _ : True => False) trivial) (H (α := Prop) (fun _ : True => False) True trivial)

-- `Lean.Order.iSup_le`: in `Prop`, f = const True over a one-point index, x = False.
theorem iSup_le_5 : ¬ drop0% Lean.Order.iSup_le 5 := fun H =>
  H (α := Prop) (fun _ : True => True) False (le_iSup (fun _ : True => True) trivial trivial)

-- `Lean.Order.le_meet_left`: in `Prop`, P = True, Q = False.
theorem le_meet_left_4 : ¬ drop0% Lean.Order.le_meet_left 4 := fun H => by
  have h := H (l := Prop) (P := True) (Q := False); clear H; prop_simp

-- `Lean.Order.le_meet_right`: in `Prop`, P = True, Q = False.
theorem le_meet_right_4 : ¬ drop0% Lean.Order.le_meet_right 4 := fun H => by
  have h := H (l := Prop) (P := True) (Q := False); clear H; prop_simp

-- `Lean.Order.le_meet_of_eq`: in `Prop`, P = Q = R = True, T = False.
theorem le_meet_of_eq_6 : ¬ drop0% Lean.Order.le_meet_of_eq 6 := fun H => by
  have h := H (l := Prop) (P := True) (Q := True) (R := True) (T := False) id id; clear H; prop_simp

-- `Lean.Order.le_meet_of_eq`: in `Prop`, P = R = True, Q = False, T = Q ⊓ R.
theorem le_meet_of_eq_7 : ¬ drop0% Lean.Order.le_meet_of_eq 7 := fun H => by
  have h := H (l := Prop) (P := True) (Q := False) (R := True) (T := False ⊓ True) rfl id; clear H; prop_simp

-- `Lean.Order.le_meet_of_eq`: in `Prop`, P = Q = True, R = False, T = Q ⊓ R.
theorem le_meet_of_eq_8 : ¬ drop0% Lean.Order.le_meet_of_eq 8 := fun H => by
  have h := H (l := Prop) (P := True) (Q := True) (R := False) (T := True ⊓ False) rfl id; clear H; prop_simp

-- `Lean.Order.meet_le_of_left_le`: in `Prop`, P = Q = True, R = False.
theorem meet_le_of_left_le_5 : ¬ drop0% Lean.Order.meet_le_of_left_le 5 := fun H => by
  have h := H (l := Prop) (P := True) (Q := True) (R := False); clear H; prop_simp

-- `Lean.Order.meet_le_of_right_le`: in `Prop`, P = Q = True, R = False.
theorem meet_le_of_right_le_5 : ¬ drop0% Lean.Order.meet_le_of_right_le 5 := fun H => by
  have h := H (l := Prop) (P := True) (Q := True) (R := False); clear H; prop_simp

-- `Lean.Order.le_join_of_le_left`: in `Prop`, P = True, Q = R = False.
theorem le_join_of_le_left_5 : ¬ drop0% Lean.Order.le_join_of_le_left 5 := fun H => by
  have h := H (l := Prop) (P := True) (Q := False) (R := False); clear H; prop_simp

-- `Lean.Order.le_join_of_le_right`: in `Prop`, P = True, Q = R = False.
theorem le_join_of_le_right_5 : ¬ drop0% Lean.Order.le_join_of_le_right 5 := fun H => by
  have h := H (l := Prop) (P := True) (Q := False) (R := False); clear H; prop_simp

-- `Lean.Order.le_of_le_of_meet_le`: in `Prop`, P = True, Q = R = False.
theorem le_of_le_of_meet_le_5 : ¬ drop0% Lean.Order.le_of_le_of_meet_le 5 := fun H => by
  have h := H (l := Prop) (P := True) (Q := False) (R := False) (meet_le_right _ _); clear H; prop_simp

-- `Lean.Order.le_of_le_of_meet_le`: in `Prop`, P = Q = True, R = False.
theorem le_of_le_of_meet_le_6 : ¬ drop0% Lean.Order.le_of_le_of_meet_le 6 := fun H => by
  have h := H (l := Prop) (P := True) (Q := True) (R := False) id; clear H; prop_simp

-- `Lean.Order.le_trans_meet`: in `Prop`, P = True, Q = R = False.
theorem le_trans_meet_5 : ¬ drop0% Lean.Order.le_trans_meet 5 := fun H => by
  have h := H (l := Prop) (P := True) (Q := False) (R := False) (meet_le_right _ _); clear H; prop_simp

-- `Lean.Order.le_trans_meet`: in `Prop`, P = Q = True, R = False.
theorem le_trans_meet_6 : ¬ drop0% Lean.Order.le_trans_meet 6 := fun H => by
  have h := H (l := Prop) (P := True) (Q := True) (R := False) id; clear H; prop_simp

-- `Lean.Order.le_iSup_of_le`: in `Prop`, P = True, Ψ = const False over a one-point index.
theorem le_iSup_of_le_6 : ¬ drop0% Lean.Order.le_iSup_of_le 6 := fun H =>
  iSup_le (fun _ : True => False) False (fun _ h => h)
    (H (l := Prop) (P := True) (Ψ := fun _ : True => False) trivial trivial)

-- `Lean.Order.le_of_le_bot`: in `Prop`, P = True, Q = False.
theorem le_of_le_bot_4 : ¬ drop0% Lean.Order.le_of_le_bot 4 := fun H => by
  have h := H (l := Prop) (P := True) (Q := False); clear H; prop_simp

-- `Lean.Order.meet_mono`: in `Prop`, P = Q = Q' = True, P' = False.
theorem meet_mono_6 : ¬ drop0% Lean.Order.meet_mono 6 := fun H => by
  have h := H (l := Prop) (P := True) (P' := False) (Q := True) (Q' := True) id; clear H; prop_simp

-- `Lean.Order.meet_mono`: in `Prop`, P = P' = Q = True, Q' = False.
theorem meet_mono_7 : ¬ drop0% Lean.Order.meet_mono 7 := fun H => by
  have h := H (l := Prop) (P := True) (P' := True) (Q := True) (Q' := False) id; clear H; prop_simp

-- `Lean.Order.meet_mono_left`: in `Prop`, P = Q = True, P' = False.
theorem meet_mono_left_5 : ¬ drop0% Lean.Order.meet_mono_left 5 := fun H => by
  have h := H (l := Prop) (P := True) (P' := False) (Q := True); clear H; prop_simp

-- `Lean.Order.meet_mono_right`: in `Prop`, P = Q = True, Q' = False.
theorem meet_mono_right_5 : ¬ drop0% Lean.Order.meet_mono_right 5 := fun H => by
  have h := H (l := Prop) (P := True) (Q := True) (Q' := False); clear H; prop_simp

-- `Lean.Order.join_mono`: in `Prop`, P = True, P' = Q = Q' = False.
theorem join_mono_6 : ¬ drop0% Lean.Order.join_mono 6 := fun H => by
  have h := H (l := Prop) (P := True) (P' := False) (Q := False) (Q' := False) id; clear H; prop_simp

-- `Lean.Order.join_mono`: in `Prop`, Q = True, P = P' = Q' = False.
theorem join_mono_7 : ¬ drop0% Lean.Order.join_mono 7 := fun H => by
  have h := H (l := Prop) (P := False) (P' := False) (Q := True) (Q' := False) id; clear H; prop_simp

-- `Lean.Order.join_mono_left`: in `Prop`, P = True, P' = Q = False.
theorem join_mono_left_5 : ¬ drop0% Lean.Order.join_mono_left 5 := fun H => by
  have h := H (l := Prop) (P := True) (P' := False) (Q := False); clear H; prop_simp

-- `Lean.Order.join_mono_right`: in `Prop`, Q = True, P = Q' = False.
theorem join_mono_right_5 : ¬ drop0% Lean.Order.join_mono_right 5 := fun H => by
  have h := H (l := Prop) (P := False) (Q := True) (Q' := False); clear H; prop_simp

-- `Lean.Order.iInf_mono`: in `Prop`, Φ = const True, Ψ = const False over a one-point index.
theorem iInf_mono_5 : ¬ drop0% Lean.Order.iInf_mono 5 := fun H =>
  iInf_le (fun _ : True => False) trivial
    (H (l := Prop) (Φ := fun _ : True => True) (Ψ := fun _ => False)
      (le_iInf (fun _ : True => True) True (fun _ _ => trivial) trivial))

-- `Lean.Order.iSup_mono`: in `Prop`, Φ = const True, Ψ = const False over a one-point index.
theorem iSup_mono_5 : ¬ drop0% Lean.Order.iSup_mono 5 := fun H =>
  iSup_le (fun _ : True => False) False (fun _ h => h)
    (H (l := Prop) (Φ := fun _ : True => True) (Ψ := fun _ => False)
      (le_iSup (fun _ : True => True) trivial trivial))

-- `Lean.Order.meet_top_le_of_le`: in `Prop`, P = True, Q = False.
theorem meet_top_le_of_le_4 : ¬ drop0% Lean.Order.meet_top_le_of_le 4 := fun H => by
  have h := H (l := Prop) (P := True) (Q := False); clear H; prop_simp

end OrderHand

namespace OrderHand

/-! ## Std.Internal.Order.Heyting (models `Prop` and `M3`) -/

-- `Lean.Order.le_himp_of_meet_le_left`: in `Prop`, a = x = True, b = False.
theorem le_himp_of_meet_le_left_5 : ¬ drop0% Lean.Order.le_himp_of_meet_le_left 5 := fun H => by
  have h := H (α := Prop) (a := True) (b := False) (x := True); clear H; prop_simp

-- `Lean.Order.meet_himp_le`: in `M3`, a = x (atom), b = o: x ⇨ o = i and x ⊓ i = x.
theorem meet_himp_le_4 : ¬ drop0% Lean.Order.meet_himp_le 4 := fun H => by
  have h := H (α := M3) (a := .x) (b := .o); revert h; m3_dec

-- `Lean.Order.le_himp`: in `Prop`, P = Q = True, R = False.
theorem le_himp_6 : ¬ drop0% Lean.Order.le_himp 6 := fun H => by
  have h := H (l := Prop) (P := True) (Q := True) (R := False); clear H; prop_simp

-- `Lean.Order.meet_le_of_le_himp`: in `M3`, P = i, Q = x, R = o (i ⊑ x ⇨ o = i).
theorem meet_le_of_le_himp_5 : ¬ drop0% Lean.Order.meet_le_of_le_himp 5 := fun H => by
  have h := H (l := M3) (P := .i) (Q := .x) (R := .o) (by m3_dec); revert h; m3_dec

-- `Lean.Order.meet_le_of_le_himp`: in `Prop`, P = Q = True, R = False.
theorem meet_le_of_le_himp_6 : ¬ drop0% Lean.Order.meet_le_of_le_himp 6 := fun H => by
  have h := H (l := Prop) (P := True) (Q := True) (R := False); clear H; prop_simp

-- `Lean.Order.meet_le_of_le_himp_left`: in `M3`, P = x, Q = i, R = o.
theorem meet_le_of_le_himp_left_5 : ¬ drop0% Lean.Order.meet_le_of_le_himp_left 5 := fun H => by
  have h := H (l := M3) (P := .x) (Q := .i) (R := .o) (by m3_dec); revert h; m3_dec

-- `Lean.Order.meet_le_of_le_himp_left`: in `Prop`, P = Q = True, R = False.
theorem meet_le_of_le_himp_left_6 : ¬ drop0% Lean.Order.meet_le_of_le_himp_left 6 := fun H => by
  have h := H (l := Prop) (P := True) (Q := True) (R := False); clear H; prop_simp

-- `Lean.Order.meet_le_of_le_himp_comm`: in `M3`, P = x, Q = i, R = o.
theorem meet_le_of_le_himp_comm_5 : ¬ drop0% Lean.Order.meet_le_of_le_himp_comm 5 := fun H => by
  have h := H (l := M3) (P := .x) (Q := .i) (R := .o) (by m3_dec); revert h; m3_dec

-- `Lean.Order.meet_le_of_le_himp_comm`: in `Prop`, P = Q = True, R = False.
theorem meet_le_of_le_himp_comm_6 : ¬ drop0% Lean.Order.meet_le_of_le_himp_comm 6 := fun H => by
  have h := H (l := Prop) (P := True) (Q := True) (R := False); clear H; prop_simp

-- `Lean.Order.himp_meet_le`: in `M3`, P = x, Q = o.
theorem himp_meet_le_4 : ¬ drop0% Lean.Order.himp_meet_le 4 := fun H => by
  have h := H (l := M3) (P := .x) (Q := .o); revert h; m3_dec

-- `Lean.Order.le_himp_mp`: in `M3`, P = Q = x, R = o.
theorem le_himp_mp_5 : ¬ drop0% Lean.Order.le_himp_mp 5 := fun H => by
  have h := H (l := M3) (P := .x) (Q := .x) (R := .o) (by m3_dec) (by m3_dec); revert h; m3_dec

-- `Lean.Order.le_himp_mp`: in `Prop`, P = Q = True, R = False.
theorem le_himp_mp_6 : ¬ drop0% Lean.Order.le_himp_mp 6 := fun H => by
  have h := H (l := Prop) (P := True) (Q := True) (R := False) id; clear H; prop_simp

-- `Lean.Order.le_himp_mp`: in `Prop`, P = True, Q = R = False (True ⊑ False ⇨ False).
theorem le_himp_mp_7 : ¬ drop0% Lean.Order.le_himp_mp 7 := fun H => by
  have h := H (l := Prop) (P := True) (Q := False) (R := False) (by prop_simp); clear H; prop_simp

-- `Lean.Order.join_meet_le`: in `M3`, P = x, Q = y, R = z, T = o: (x ⊔ y) ⊓ z = z.
theorem join_meet_le_6 : ¬ drop0% Lean.Order.join_meet_le 6 := fun H => by
  have h := H (l := M3) (P := .x) (Q := .y) (R := .z) (T := .o) (by m3_dec) (by m3_dec)
  revert h; m3_dec

-- `Lean.Order.join_meet_le`: in `Prop`, P = R = True, Q = T = False.
theorem join_meet_le_7 : ¬ drop0% Lean.Order.join_meet_le 7 := fun H => by
  have h := H (l := Prop) (P := True) (Q := False) (R := True) (T := False) (by prop_simp)
  clear H; prop_simp

-- `Lean.Order.join_meet_le`: in `Prop`, Q = R = True, P = T = False.
theorem join_meet_le_8 : ¬ drop0% Lean.Order.join_meet_le 8 := fun H => by
  have h := H (l := Prop) (P := False) (Q := True) (R := True) (T := False) (by prop_simp)
  clear H; prop_simp

-- `Lean.Order.meet_join_le_left`: in `M3`, P = x, Q = y, R = z, T = o.
theorem meet_join_le_left_6 : ¬ drop0% Lean.Order.meet_join_le_left 6 := fun H => by
  have h := H (l := M3) (P := .x) (Q := .y) (R := .z) (T := .o) (by m3_dec) (by m3_dec)
  revert h; m3_dec

-- `Lean.Order.meet_join_le_left`: in `Prop`, P = R = True, Q = T = False.
theorem meet_join_le_left_7 : ¬ drop0% Lean.Order.meet_join_le_left 7 := fun H => by
  have h := H (l := Prop) (P := True) (Q := False) (R := True) (T := False) (by prop_simp)
  clear H; prop_simp

-- `Lean.Order.meet_join_le_left`: in `Prop`, Q = R = True, P = T = False.
theorem meet_join_le_left_8 : ¬ drop0% Lean.Order.meet_join_le_left 8 := fun H => by
  have h := H (l := Prop) (P := False) (Q := True) (R := True) (T := False) (by prop_simp)
  clear H; prop_simp

-- `Lean.Order.meet_join_le`: in `M3`, P = z, Q = x, R = y, T = o: z ⊓ (x ⊔ y) = z.
theorem meet_join_le_6 : ¬ drop0% Lean.Order.meet_join_le 6 := fun H => by
  have h := H (l := M3) (P := .z) (Q := .x) (R := .y) (T := .o) (by m3_dec) (by m3_dec)
  revert h; m3_dec

-- `Lean.Order.meet_join_le`: in `Prop`, P = Q = True, R = T = False.
theorem meet_join_le_7 : ¬ drop0% Lean.Order.meet_join_le 7 := fun H => by
  have h := H (l := Prop) (P := True) (Q := True) (R := False) (T := False) (by prop_simp)
  clear H; prop_simp

-- `Lean.Order.meet_join_le`: in `Prop`, P = R = True, Q = T = False.
theorem meet_join_le_8 : ¬ drop0% Lean.Order.meet_join_le 8 := fun H => by
  have h := H (l := Prop) (P := True) (Q := False) (R := True) (T := False) (by prop_simp)
  clear H; prop_simp

-- `Lean.Order.meet_join_le_right`: in `M3`, P = z, Q = x, R = y, T = o.
theorem meet_join_le_right_6 : ¬ drop0% Lean.Order.meet_join_le_right 6 := fun H => by
  have h := H (l := M3) (P := .z) (Q := .x) (R := .y) (T := .o) (by m3_dec) (by m3_dec)
  revert h; m3_dec

-- `Lean.Order.meet_join_le_right`: in `Prop`, P = Q = True, R = T = False.
theorem meet_join_le_right_7 : ¬ drop0% Lean.Order.meet_join_le_right 7 := fun H => by
  have h := H (l := Prop) (P := True) (Q := True) (R := False) (T := False) (by prop_simp)
  clear H; prop_simp

-- `Lean.Order.meet_join_le_right`: in `Prop`, P = R = True, Q = T = False.
theorem meet_join_le_right_8 : ¬ drop0% Lean.Order.meet_join_le_right 8 := fun H => by
  have h := H (l := Prop) (P := True) (Q := False) (R := True) (T := False) (by prop_simp)
  clear H; prop_simp

-- `Lean.Order.himp_mono`: removable, `⇨` (an upper adjoint of the meet, i.e. a supremum of
-- `{x | P ⊓ x ⊑ P'}`) is antitone/monotone in any complete lattice.
theorem himp_mono_6 : drop% Lean.Order.himp_mono 6 := by
  intro l _ P P' Q Q' h1 h2
  exact sup_le _ fun x (hx : P ⊓ x ⊑ P') =>
    PreservesSup.le_upperAdjoint (meet Q) (rel_trans (meet_mono_left h1) (rel_trans hx h2))

-- `Lean.Order.himp_mono`: in `Prop`, Q = True, P = P' = Q' = False.
theorem himp_mono_7 : ¬ drop0% Lean.Order.himp_mono 7 := fun H => by
  have h := H (l := Prop) (P := False) (P' := False) (Q := True) (Q' := False) id
  clear H; prop_simp

-- `Lean.Order.himp_mono`: in `Prop`, P = Q = P' = True, Q' = False.
theorem himp_mono_8 : ¬ drop0% Lean.Order.himp_mono 8 := fun H => by
  have h := H (l := Prop) (P := True) (P' := True) (Q := True) (Q' := False) id
  clear H; prop_simp

-- `Lean.Order.himp_mono_left`: removable, `⇨` is antitone in its first argument in any complete
-- lattice.
theorem himp_mono_left_5 : drop% Lean.Order.himp_mono_left 5 := by
  intro l _ P P' Q h
  exact sup_le _ fun x (hx : P ⊓ x ⊑ Q) =>
    PreservesSup.le_upperAdjoint (meet P') (rel_trans (meet_mono_left h) hx)

-- `Lean.Order.himp_mono_left`: in `Prop`, P' = True, P = Q = False.
theorem himp_mono_left_6 : ¬ drop0% Lean.Order.himp_mono_left 6 := fun H => by
  have h := H (l := Prop) (P := False) (P' := True) (Q := False); clear H; prop_simp

-- `Lean.Order.himp_mono_right`: removable, `⇨` is monotone in its second argument in any complete
-- lattice.
theorem himp_mono_right_5 : drop% Lean.Order.himp_mono_right 5 := by
  intro l _ P Q Q' h
  exact sup_le _ fun x (hx : P ⊓ x ⊑ Q) =>
    PreservesSup.le_upperAdjoint (meet P) (rel_trans hx h)

-- `Lean.Order.himp_mono_right`: in `Prop`, P = Q = True, Q' = False.
theorem himp_mono_right_6 : ¬ drop0% Lean.Order.himp_mono_right 6 := fun H => by
  have h := H (l := Prop) (P := True) (Q := True) (Q' := False); clear H; prop_simp

-- `Lean.Order.meet_join_left`: in `M3`, P = x, Q = y, R = z: x ⊓ i = x ≠ o.
theorem meet_join_left_5 : ¬ drop0% Lean.Order.meet_join_left 5 := fun H => by
  have h := H (l := M3) (P := .x) (Q := .y) (R := .z); revert h; m3_dec

-- `Lean.Order.join_meet_left`: in `M3`, P = x, Q = y, R = z: x ⊔ o = x ≠ i.
theorem join_meet_left_5 : ¬ drop0% Lean.Order.join_meet_left 5 := fun H => by
  have h := H (l := M3) (P := .x) (Q := .y) (R := .z); revert h; m3_dec

-- `Lean.Order.meet_join_right`: in `M3`, P = x, Q = y, R = z: i ⊓ z = z ≠ o.
theorem meet_join_right_5 : ¬ drop0% Lean.Order.meet_join_right 5 := fun H => by
  have h := H (l := M3) (P := .x) (Q := .y) (R := .z); revert h; m3_dec

-- `Lean.Order.join_meet_right`: in `M3`, P = x, Q = y, R = z: o ⊔ z = z ≠ i.
theorem join_meet_right_5 : ¬ drop0% Lean.Order.join_meet_right 5 := fun H => by
  have h := H (l := M3) (P := .x) (Q := .y) (R := .z); revert h; m3_dec

-- `Lean.Order.top_himp`: removable, `⊤ ⇨ P` is the supremum of `{x | ⊤ ⊓ x ⊑ P} = {x | x ⊑ P}`
-- in any complete lattice.
theorem top_himp_3 : drop% Lean.Order.top_himp 3 := fun {_} _ {P} => top_himp' P

-- `Lean.Order.himp_meet_himp_le`: in `M3`, P = i, Q = x, R = o: x ⊓ i = x ⋢ o = i ⇨ o.
theorem himp_meet_himp_le_5 : ¬ drop0% Lean.Order.himp_meet_himp_le 5 := fun H => by
  have h := H (l := M3) (P := .i) (Q := .x) (R := .o); revert h; m3_dec

-- `Lean.Order.meet_himp_le_meet`: in `M3`, P' = x, Q' = o.
theorem meet_himp_le_meet_4 : ¬ drop0% Lean.Order.meet_himp_le_meet 4 := fun H => by
  have h := H (l := M3) (P' := .x) (Q' := .o); revert h; m3_dec

-- `Lean.Order.meet_le_meet_of_le_himp`: in `M3`, P = P' = x, Q = i, Q' = o.
theorem meet_le_meet_of_le_himp_6 : ¬ drop0% Lean.Order.meet_le_meet_of_le_himp 6 := fun H => by
  have h := H (l := M3) (P := .x) (P' := .x) (Q := .i) (Q' := .o) (by m3_dec) (by m3_dec)
  revert h; m3_dec

-- `Lean.Order.meet_le_meet_of_le_himp`: in `Prop`, P = Q = True, P' = Q' = False.
theorem meet_le_meet_of_le_himp_7 : ¬ drop0% Lean.Order.meet_le_meet_of_le_himp 7 := fun H => by
  have h := H (l := Prop) (P := True) (P' := False) (Q := True) (Q' := False) (by prop_simp)
  clear H; prop_simp

-- `Lean.Order.meet_le_meet_of_le_himp`: in `Prop`, P = P' = Q = True, Q' = False.
theorem meet_le_meet_of_le_himp_8 : ¬ drop0% Lean.Order.meet_le_meet_of_le_himp 8 := fun H => by
  have h := H (l := Prop) (P := True) (P' := True) (Q := True) (Q' := False) id
  clear H; prop_simp

-- `Lean.Order.CompleteLattice.ofProp_himp_ofProp`: removable, `⌜φ⌝` is `⊤` or `⊥`, and
-- `⊤ ⇨ P = P`, `⊥ ⇨ P = ⊤` hold in any complete lattice.
theorem CompleteLattice_ofProp_himp_ofProp_2 :
    drop% Lean.Order.CompleteLattice.ofProp_himp_ofProp 2 :=
  fun {_} _ {φ₁ φ₂} => ofProp_himp' φ₁ φ₂

-- `Lean.Order.himp_ofProp`: removable, as for `Lean.Order.CompleteLattice.ofProp_himp_ofProp`.
theorem himp_ofProp_2 : drop% Lean.Order.himp_ofProp 2 :=
  fun {_} _ {φ₁ φ₂} => ofProp_himp' φ₁ φ₂

-- `Lean.Order.le_himp_comm`: in `Prop`, P = Q = True, R = False.
theorem le_himp_comm_6 : ¬ drop0% Lean.Order.le_himp_comm 6 := fun H => by
  have h := H (l := Prop) (P := True) (Q := True) (R := False); clear H; prop_simp

-- `Lean.Order.le_himp_of_meet_le_comm`: in `Prop`, P = Q = True, R = False.
theorem le_himp_of_meet_le_comm_6 : ¬ drop0% Lean.Order.le_himp_of_meet_le_comm 6 := fun H => by
  have h := H (l := Prop) (P := True) (Q := True) (R := False); clear H; prop_simp

-- `Lean.Order.top_le_himp_iff`: in `M3`, P = x, Q = o: ⊤ ⊑ x ⇨ o = i but x ⋢ o.
theorem top_le_himp_iff_2 : ¬ drop0% Lean.Order.top_le_himp_iff 2 := fun H => by
  have h := (H (l := M3) .x .o).1 (by m3_dec); revert h; m3_dec

end OrderHand

namespace OrderHand

/-! ## Std.Internal.Order.OfProp, Prop, Product (model `Prop`) -/

-- `Lean.Order.CompleteLattice.top_le_ofProp`: in `Prop`, p = False: ⊤ = True ⋢ False.
theorem CompleteLattice_top_le_ofProp_3 : ¬ drop0% Lean.Order.CompleteLattice.top_le_ofProp 3 :=
  fun H => by have h := H (l := Prop) False; clear H; prop_simp

-- `Lean.Order.top_le_ofProp`: in `Prop`, p = False.
theorem top_le_ofProp_3 : ¬ drop0% Lean.Order.top_le_ofProp 3 :=
  fun H => by have h := H (l := Prop) False; clear H; prop_simp

-- `Lean.Order.CompleteLattice.le_ofProp`: in `Prop`, x = True, p = False.
theorem CompleteLattice_le_ofProp_4 : ¬ drop0% Lean.Order.CompleteLattice.le_ofProp 4 :=
  fun H => by have h := H (l := Prop) True False; clear H; prop_simp

-- `Lean.Order.le_ofProp`: in `Prop`, x = True, p = False.
theorem le_ofProp_4 : ¬ drop0% Lean.Order.le_ofProp 4 :=
  fun H => by have h := H (l := Prop) True False; clear H; prop_simp

-- `Lean.Order.CompleteLattice.ofProp_le`: in `Prop`, p = True, rhs = False.
theorem CompleteLattice_ofProp_le_4 : ¬ drop0% Lean.Order.CompleteLattice.ofProp_le 4 :=
  fun H => by have h := H (l := Prop) True False; clear H; prop_simp

-- `Lean.Order.ofProp_le`: in `Prop`, p = True, rhs = False.
theorem ofProp_le_4 : ¬ drop0% Lean.Order.ofProp_le 4 :=
  fun H => by have h := H (l := Prop) True False; clear H; prop_simp

-- `Lean.Order.CompleteLattice.le_of_le_ofProp`: in `Prop`, φ = False, Q = True, R = False.
theorem CompleteLattice_le_of_le_ofProp_5 :
    ¬ drop0% Lean.Order.CompleteLattice.le_of_le_ofProp 5 := fun H => by
  have h := H (l := Prop) (Q := True) (R := False) (φ := False) False.elim; clear H; prop_simp

-- `Lean.Order.CompleteLattice.le_of_le_ofProp`: in `Prop`, φ = Q = True, R = False.
theorem CompleteLattice_le_of_le_ofProp_6 :
    ¬ drop0% Lean.Order.CompleteLattice.le_of_le_ofProp 6 := fun H => by
  have h := H (l := Prop) (Q := True) (R := False) (φ := True) (by prop_simp); clear H; prop_simp

-- `Lean.Order.ofProp_elim`: in `Prop`, φ = False, Q = True, R = False.
theorem ofProp_elim_5 : ¬ drop0% Lean.Order.ofProp_elim 5 := fun H => by
  have h := H (l := Prop) (Q := True) (R := False) (φ := False) False.elim; clear H; prop_simp

-- `Lean.Order.ofProp_elim`: in `Prop`, φ = Q = True, R = False.
theorem ofProp_elim_6 : ¬ drop0% Lean.Order.ofProp_elim 6 := fun H => by
  have h := H (l := Prop) (Q := True) (R := False) (φ := True) (by prop_simp); clear H; prop_simp

-- `Lean.Order.CompleteLattice.ofProp_mono`: in `Prop`, φ₁ = True, φ₂ = False.
theorem CompleteLattice_ofProp_mono_4 : ¬ drop0% Lean.Order.CompleteLattice.ofProp_mono 4 :=
  fun H => by have h := H (l := Prop) (φ₁ := True) (φ₂ := False); clear H; prop_simp

-- `Lean.Order.ofProp_mono`: in `Prop`, φ₁ = True, φ₂ = False.
theorem ofProp_mono_4 : ¬ drop0% Lean.Order.ofProp_mono 4 :=
  fun H => by have h := H (l := Prop) (φ₁ := True) (φ₂ := False); clear H; prop_simp

-- `Lean.Order.CompleteLattice.ofProp_imp`: in `Prop`, p₁ = True, p₂ = False.
theorem CompleteLattice_ofProp_imp_4 : ¬ drop0% Lean.Order.CompleteLattice.ofProp_imp 4 :=
  fun H => by have h := H (l := Prop) True False; clear H; prop_simp

-- `Lean.Order.CompleteLattice.ofProp_congr`: in `Prop`, φ₁ = True, φ₂ = False.
theorem CompleteLattice_ofProp_congr_4 : ¬ drop0% Lean.Order.CompleteLattice.ofProp_congr 4 :=
  fun H => by have h := H (l := Prop) (φ₁ := True) (φ₂ := False); clear H; prop_simp

-- `Lean.Order.ofProp_congr`: in `Prop`, φ₁ = True, φ₂ = False.
theorem ofProp_congr_4 : ¬ drop0% Lean.Order.ofProp_congr 4 :=
  fun H => by have h := H (l := Prop) (φ₁ := True) (φ₂ := False); clear H; prop_simp

-- `Lean.Order.CompleteLattice.ofProp_meet_le`: in `Prop`, φ = Q = True, R = False.
theorem CompleteLattice_ofProp_meet_le_5 : ¬ drop0% Lean.Order.CompleteLattice.ofProp_meet_le 5 :=
  fun H => by have h := H (l := Prop) (Q := True) (R := False) (φ := True); clear H; prop_simp

-- `Lean.Order.CompleteLattice.meet_ofProp_le`: in `Prop`, φ = Q = True, R = False.
theorem CompleteLattice_meet_ofProp_le_5 : ¬ drop0% Lean.Order.CompleteLattice.meet_ofProp_le 5 :=
  fun H => by have h := H (l := Prop) (Q := True) (R := False) (φ := True); clear H; prop_simp

-- `Lean.Order.ofProp_meet_le`: in `Prop`, p = x = True, rhs = False.
theorem ofProp_meet_le_5 : ¬ drop0% Lean.Order.ofProp_meet_le 5 :=
  fun H => by have h := H (l := Prop) True True False; clear H; prop_simp

-- `Lean.Order.ofProp_meet_le_left`: in `Prop`, φ = Q = True, R = False.
theorem ofProp_meet_le_left_5 : ¬ drop0% Lean.Order.ofProp_meet_le_left 5 :=
  fun H => by have h := H (l := Prop) (Q := True) (R := False) (φ := True); clear H; prop_simp

-- `Lean.Order.ofProp_meet_le_right`: in `Prop`, φ = Q = True, R = False.
theorem ofProp_meet_le_right_5 : ¬ drop0% Lean.Order.ofProp_meet_le_right 5 :=
  fun H => by have h := H (l := Prop) (Q := True) (R := False) (φ := True); clear H; prop_simp

-- `Lean.Order.CompleteLattice.ofProp_eq_top`: in `Prop`, φ = False: False ≠ True.
theorem CompleteLattice_ofProp_eq_top_3 : ¬ drop0% Lean.Order.CompleteLattice.ofProp_eq_top 3 :=
  fun H => by have h := H (l := Prop) (φ := False); clear H; prop_simp

-- `Lean.Order.ofProp_eq_top`: in `Prop`, φ = False.
theorem ofProp_eq_top_3 : ¬ drop0% Lean.Order.ofProp_eq_top 3 :=
  fun H => by have h := H (l := Prop) (φ := False); clear H; prop_simp

-- `Lean.Order.le_iSup_prop`: in `Prop`, p = True, a = False (the supremum over `False` is `⊥`).
theorem le_iSup_prop_5 : ¬ drop0% Lean.Order.le_iSup_prop 5 := fun H =>
  iSup_le (fun _ : False => True) False (fun h => h.elim)
    (H (l := Prop) True False (fun _ => True) (fun h => h.elim) trivial)

-- `Lean.Order.le_iSup_prop`: in `Prop`, p = a = True, b = const False.
theorem le_iSup_prop_6 : ¬ drop0% Lean.Order.le_iSup_prop 6 := fun H =>
  iSup_le (fun _ : True => False) False (fun _ h => h)
    (H (l := Prop) True True (fun _ => False) (by prop_simp) trivial)

-- `Lean.Order.le_apply_of_point_meet_le`: σ = Unit, β = `Prop`, pre = True, Q = const False.
theorem le_apply_of_point_meet_le_6 : ¬ drop0% Lean.Order.le_apply_of_point_meet_le 6 := fun H =>
  H (σ := Unit) (β := Prop) () True (fun _ => False) trivial

-- `Lean.Order.point_meet_le_of_le_apply`: σ = Unit, β = `Prop`, pre = True, Q = const False.
theorem point_meet_le_of_le_apply_6 : ¬ drop0% Lean.Order.point_meet_le_of_le_apply 6 :=
  fun H => by have h := H (σ := Unit) (β := Prop) () True (fun _ => False) (); clear H; prop_simp

-- `Lean.Order.le_of_forall_le`: σ = Unit, β = `Prop`, f = const True, g = const False.
theorem le_of_forall_le_5 : ¬ drop0% Lean.Order.le_of_forall_le 5 := fun H =>
  H (σ := Unit) (β := Prop) (f := fun _ => True) (g := fun _ => False) () trivial

-- `Lean.Order.top_le_of_forall_top_le`: σ = Unit, β = `Prop`, g = const False.
theorem top_le_of_forall_top_le_4 : ¬ drop0% Lean.Order.top_le_of_forall_top_le 4 := fun H => by
  have h := H (σ := Unit) (β := Prop) (g := fun _ => False) ()
  rw [top_apply] at h; clear H; prop_simp

-- `Lean.Order.le_forall`: β = True, p = True, q = const False.
theorem le_forall_3 : ¬ drop0% Lean.Order.le_forall 3 := fun H =>
  H (β := True) True (fun _ => False) trivial trivial

-- `Lean.Order.le_exists_prop`: p = True, a = False.
theorem le_exists_prop_3 : ¬ drop0% Lean.Order.le_exists_prop 3 := fun H =>
  (H True False (fun _ => True) (fun h => h.elim) trivial).elim fun h _ => h

-- `Lean.Order.le_exists_prop`: p = a = True, b = const False.
theorem le_exists_prop_4 : ¬ drop0% Lean.Order.le_exists_prop 4 := fun H =>
  (H True True (fun _ => False) id trivial).elim fun _ h => h

-- `Lean.Order.PredTrans.ext`: the transformers `fun _ _ => True` and `fun _ _ => False` differ.
theorem PredTrans_ext_5 : ¬ drop0% Lean.Order.PredTrans.ext 5 := fun H => by
  have h := congrArg (fun t : PredTrans Prop Prop Unit => t.apply (fun _ => True) True)
    (H (x := ⟨fun _ _ => True⟩) (y := ⟨fun _ _ => False⟩))
  exact cast h trivial

end OrderHand

namespace OrderHand

/-! ## Std.Internal.Order.Basic / PreservesSup (models `Prop`, `M3`) -/

-- `Lean.Order.PreservesSup.map_sup`: the constant `True` map on `Prop` does not preserve `⊥`.
theorem PreservesSup_map_sup_3 : ¬ drop0% Lean.Order.PreservesSup.map_sup 3 := fun H =>
  not_ps_true ⟨fun s => H (f := fun _ : Prop => True) s⟩

-- `Lean.Order.PreservesSup.le_upperAdjoint`: in `Prop`, f = id, b = False, x = True.
theorem PreservesSup_le_upperAdjoint_5 : ¬ drop0% Lean.Order.PreservesSup.le_upperAdjoint 5 :=
  fun H => by
    have h := H (α := Prop) id (b := False) (x := True)
    rw [PreservesSup.upperAdjoint_id] at h; exact h trivial

-- `Lean.Order.PreservesSup.upperAdjoint_le`: in `Prop`, f = const True, b = False.
theorem PreservesSup_upperAdjoint_le_3 : ¬ drop0% Lean.Order.PreservesSup.upperAdjoint_le 3 :=
  fun H => H (α := Prop) (fun _ => True) False trivial

-- `Lean.Order.PreservesSup.map_mono`: in `Prop`, f = Not (antitone), b = False, b' = True.
theorem PreservesSup_map_mono_3 : ¬ drop0% Lean.Order.PreservesSup.map_mono 3 :=
  fun H => H (α := Prop) Not (b := False) (b' := True) (fun _ => trivial) id trivial

-- `Lean.Order.PreservesSup.map_mono`: in `Prop`, f = id, b = True, b' = False.
theorem PreservesSup_map_mono_6 : ¬ drop0% Lean.Order.PreservesSup.map_mono 6 :=
  fun H => H (α := Prop) id (b := True) (b' := False) trivial

-- `Lean.Order.PreservesSup.upperAdjoint_mono`: removable, `upperAdjoint f b` is the supremum of
-- `{x | f x ⊑ b}`, which grows with b for any f.
theorem PreservesSup_upperAdjoint_mono_3 : drop% Lean.Order.PreservesSup.upperAdjoint_mono 3 := by
  intro α _ f b b' h
  exact sup_le _ fun x (hx : f x ⊑ b) => PreservesSup.le_upperAdjoint f (rel_trans hx h)

-- `Lean.Order.PreservesSup.upperAdjoint_mono`: in `Prop`, f = id, b = True, b' = False.
theorem PreservesSup_upperAdjoint_mono_6 : ¬ drop0% Lean.Order.PreservesSup.upperAdjoint_mono 6 :=
  fun H => by
    have h := H (α := Prop) id (b := True) (b' := False)
    rw [PreservesSup.upperAdjoint_id, PreservesSup.upperAdjoint_id] at h; exact h trivial

-- `Lean.Order.PreservesSup.upperAdjoint_comp_apply`: in `Prop`, ε = Bool, f = const True,
-- X b = (b = true), e = true: no Y has f ∘ Y ⊑ X, so the left side is `False`; the right side is
-- `upperAdjoint f True = True`.
theorem PreservesSup_upperAdjoint_comp_apply_4 :
    ¬ drop0% Lean.Order.PreservesSup.upperAdjoint_comp_apply 4 := fun H => by
  have h1 : True ⊑ PreservesSup.upperAdjoint (fun _ : Prop => True) ((fun b : Bool => b = true) true) :=
    PreservesSup.le_upperAdjoint _ (fun _ => rfl)
  have h2 : PreservesSup.upperAdjoint (Function.comp (fun _ : Prop => True)) (fun b : Bool => b = true)
      ⊑ fun _ => False :=
    ua_le _ _ _ fun Y hY => absurd (hY false trivial) Bool.false_ne_true
  have h3 := h2 true
  rw [H (α := Prop) (fun _ => True) (fun b : Bool => b = true) true] at h3
  exact h3 (h1 trivial)

-- `Lean.Order.PreservesSup.upperAdjoint_prodMap_fst`: removable, the first component only needs
-- some b with g b ⊑ E.2, and `g ⊥ = ⊥` since g preserves suprema.
theorem PreservesSup_upperAdjoint_prodMap_fst_6 :
    drop% Lean.Order.PreservesSup.upperAdjoint_prodMap_fst 6 :=
  fun {_} _ {_} _ f g _ E => prodMap_fst' f g E

-- `Lean.Order.PreservesSup.upperAdjoint_prodMap_fst`: in `Prop × Prop`, f = id, g = const True,
-- E = (True, False): nothing satisfies g b ⊑ False, so the first component is `False`, not `True`.
theorem PreservesSup_upperAdjoint_prodMap_fst_7 :
    ¬ drop0% Lean.Order.PreservesSup.upperAdjoint_prodMap_fst 7 := fun H => by
  have h := H (α := Prop) (β := Prop) id (fun _ => True) (True, False)
  rw [PreservesSup.upperAdjoint_id] at h
  have h2 : PreservesSup.upperAdjoint (Prod.map (id : Prop → Prop) (fun _ : Prop => True))
      (True, False) ⊑ (False, False) :=
    ua_le _ _ _ fun _ hx => (hx.2 trivial).elim
  have h3 := h2.1; rw [h] at h3; exact h3 trivial

-- `Lean.Order.PreservesSup.upperAdjoint_prodMap_snd`: in `Prop × Prop`, f = const True, g = id,
-- E = (False, True).
theorem PreservesSup_upperAdjoint_prodMap_snd_6 :
    ¬ drop0% Lean.Order.PreservesSup.upperAdjoint_prodMap_snd 6 := fun H => by
  have h := H (α := Prop) (β := Prop) (fun _ => True) id (False, True)
  rw [PreservesSup.upperAdjoint_id] at h
  have h2 : PreservesSup.upperAdjoint (Prod.map (fun _ : Prop => True) (id : Prop → Prop))
      (False, True) ⊑ (False, False) :=
    ua_le _ _ _ fun _ hx => (hx.1 trivial).elim
  have h3 := h2.2; rw [h] at h3; exact h3 trivial

-- `Lean.Order.PreservesSup.upperAdjoint_prodMap_snd`: removable, symmetric to
-- `Lean.Order.PreservesSup.upperAdjoint_prodMap_fst` (only `f ⊥ = ⊥` is needed).
theorem PreservesSup_upperAdjoint_prodMap_snd_7 :
    drop% Lean.Order.PreservesSup.upperAdjoint_prodMap_snd 7 :=
  fun {_} _ {_} _ f g _ E => prodMap_snd' f g E

-- `Lean.Order.iSup_meet_le`: in `M3`, ι = Bool, Φ = (x, y), P = z, R = o: ⨆ Φ = i and i ⊓ z = z.
theorem iSup_meet_le_6 : ¬ drop0% Lean.Order.iSup_meet_le 6 := fun H => by
  let Φ : Bool → M3 := fun b => if b then .x else .y
  have h := H (α := M3) (ι := Bool) (P := .z) (R := .o) (Φ := Φ) (fun b => by cases b <;> m3_dec)
  have hs : M3.i ⊑ iSup Φ := M3.ub_xy _ (le_iSup Φ true) (le_iSup Φ false)
  have := rel_trans (meet_mono_left (Q := M3.z) hs) h
  revert this; m3_dec

-- `Lean.Order.iSup_meet_le`: in `Prop`, ι = Unit, Φ = const True, P = True, R = False.
theorem iSup_meet_le_7 : ¬ drop0% Lean.Order.iSup_meet_le 7 := fun H =>
  H (α := Prop) (ι := Unit) (P := True) (R := False) (Φ := fun _ => True)
    (le_meet True _ True (le_iSup (fun _ : Unit => True) ()) id trivial)

-- `Lean.Order.instPreservesSupForallComp`: ε = Unit, f = const True on `Prop`.
theorem instPreservesSupForallComp_4 : ¬ drop0% Lean.Order.instPreservesSupForallComp 4 :=
  fun H => absurd (H (α := Prop) (ε := Unit) (fun _ => True))
    (not_ps_of _ (fun _ : Unit => False) (fun _ h => h () trivial))

-- `Lean.Order.instPreservesSupForallMeet`: σ = Unit, β = const `M3`, a = const x (M3 is no frame).
theorem instPreservesSupForallMeet_3 : ¬ drop0% Lean.Order.instPreservesSupForallMeet 3 :=
  fun H => not_ps_meet (fun _ => M3.x) (fun _ => M3.o) (fun _ => M3.x) (fun _ => M3.y)
    (fun _ => M3.z) (fun w h1 h2 s => M3.lb_xy _ (h1 s) (h2 s))
    (fun w h1 h2 s => M3.lb_xz _ (h1 s) (h2 s)) (fun u h1 h2 s => M3.ub_yz _ (h1 s) (h2 s))
    (fun _ => rel_refl) (fun h => absurd (h ()) (by decide))
    (H (σ := Unit) (β := fun _ => M3) (fun _ => M3.x))

-- `Lean.Order.instPreservesSupPProdMeet`: α = `M3`, β = `Prop`, p = ⟨x, True⟩.
theorem instPreservesSupPProdMeet_4 : ¬ drop0% Lean.Order.instPreservesSupPProdMeet 4 :=
  fun H => not_ps_meet (⟨M3.x, True⟩ : M3 ×' Prop) ⟨M3.o, True⟩ ⟨M3.x, True⟩ ⟨M3.y, True⟩
    ⟨M3.z, True⟩ (fun _ h1 h2 => ⟨M3.lb_xy _ h1.1 h2.1, h1.2⟩)
    (fun _ h1 h2 => ⟨M3.lb_xz _ h1.1 h2.1, h1.2⟩) (fun _ h1 h2 => ⟨M3.ub_yz _ h1.1 h2.1, h1.2⟩)
    ⟨rel_refl, rel_refl⟩ (fun h => absurd h.1 (by decide))
    (H (α := M3) (β := Prop) ⟨M3.x, True⟩)

-- `Lean.Order.instPreservesSupPProdMeet`: α = `Prop`, β = `M3`, p = ⟨True, x⟩.
theorem instPreservesSupPProdMeet_5 : ¬ drop0% Lean.Order.instPreservesSupPProdMeet 5 :=
  fun H => not_ps_meet (⟨True, M3.x⟩ : Prop ×' M3) ⟨True, M3.o⟩ ⟨True, M3.x⟩ ⟨True, M3.y⟩
    ⟨True, M3.z⟩ (fun _ h1 h2 => ⟨h1.1, M3.lb_xy _ h1.2 h2.2⟩)
    (fun _ h1 h2 => ⟨h1.1, M3.lb_xz _ h1.2 h2.2⟩) (fun _ h1 h2 => ⟨h1.1, M3.ub_yz _ h1.2 h2.2⟩)
    ⟨rel_refl, rel_refl⟩ (fun h => absurd h.2 (by decide))
    (H (α := Prop) (β := M3) ⟨True, M3.x⟩)

-- `Lean.Order.instPreservesSupProdMeet`: α = `M3`, β = `Prop`, p = (x, True).
theorem instPreservesSupProdMeet_4 : ¬ drop0% Lean.Order.instPreservesSupProdMeet 4 :=
  fun H => not_ps_meet ((M3.x, True) : M3 × Prop) (M3.o, True) (M3.x, True) (M3.y, True)
    (M3.z, True) (fun _ h1 h2 => ⟨M3.lb_xy _ h1.1 h2.1, h1.2⟩)
    (fun _ h1 h2 => ⟨M3.lb_xz _ h1.1 h2.1, h1.2⟩) (fun _ h1 h2 => ⟨M3.ub_yz _ h1.1 h2.1, h1.2⟩)
    ⟨rel_refl, rel_refl⟩ (fun h => absurd h.1 (by decide))
    (H (α := M3) (β := Prop) (M3.x, True))

-- `Lean.Order.instPreservesSupProdMeet`: α = `Prop`, β = `M3`, p = (True, x).
theorem instPreservesSupProdMeet_5 : ¬ drop0% Lean.Order.instPreservesSupProdMeet 5 :=
  fun H => not_ps_meet ((True, M3.x) : Prop × M3) (True, M3.o) (True, M3.x) (True, M3.y)
    (True, M3.z) (fun _ h1 h2 => ⟨h1.1, M3.lb_xy _ h1.2 h2.2⟩)
    (fun _ h1 h2 => ⟨h1.1, M3.lb_xz _ h1.2 h2.2⟩) (fun _ h1 h2 => ⟨h1.1, M3.ub_yz _ h1.2 h2.2⟩)
    ⟨rel_refl, rel_refl⟩ (fun h => absurd h.2 (by decide))
    (H (α := Prop) (β := M3) (True, M3.x))

-- `Lean.Order.instPreservesSupProdMap`: f = const True, g = id on `Prop`.
theorem instPreservesSupProdMap_6 : ¬ drop0% Lean.Order.instPreservesSupProdMap 6 :=
  fun H => absurd (H (α := Prop) (β := Prop) (fun _ => True) id)
    (not_ps_of _ (False, False) (fun _ h => h.1 trivial))

-- `Lean.Order.instPreservesSupProdMap`: f = id, g = const True on `Prop`.
theorem instPreservesSupProdMap_7 : ¬ drop0% Lean.Order.instPreservesSupProdMap 7 :=
  fun H => absurd (H (α := Prop) (β := Prop) id (fun _ => True))
    (not_ps_of _ (False, False) (fun _ h => h.2 trivial))

end OrderHand

namespace OrderHand

/-! ## Std.Internal.Order.FrameClosure (models `Prop`, `Bool → Prop` with `sw`) -/

section FrameHelpers
universe v w x
variable {Pred : Type u} [CompleteLattice Pred] {EPosts : Type v} [CompleteLattice EPosts]
  {β : Type w} {R : Type x} {opE : R → EPosts → EPosts}

-- upper bound of a frame closure through one resource r
theorem fc_le (op : R → Pred → Pred) [FrameOp op EPosts opE] (t : PredTrans Pred EPosts β)
    (Q : β → Pred) (E : EPosts) (r : R) (y : Pred)
    (h : ∀ x, op r x ⊑ t.apply (fun a => op r (Q a)) (opE r E) → x ⊑ y) :
    (t.frameClosure op).apply Q E ⊑ y :=
  rel_trans (iInf_le _ r) (ua_le _ _ _ h)

end FrameHelpers

-- `Lean.Order.FrameOp.preservesSup`: op = const True on `Prop` does not preserve suprema.
theorem FrameOp_preservesSup_7 : ¬ drop0% Lean.Order.FrameOp.preservesSup 7 := fun H =>
  not_ps_true (@H Prop _ Unit (fun _ _ => True) Prop instCompleteLatticeProp (fun _ => id) ())

-- `Lean.Order.FrameOp.preservesSupE`: opE = const True on `Prop`.
theorem FrameOp_preservesSupE_7 : ¬ drop0% Lean.Order.FrameOp.preservesSupE 7 := fun H =>
  not_ps_true (@H Prop instCompleteLatticeProp Unit (fun _ => id) Prop _ (fun _ _ => True) ())

-- `Lean.Order.instPreservesSupForallPointwise`: opE = const True on `Prop`, ε = Unit.
theorem instPreservesSupForallPointwise_4 :
    ¬ drop0% Lean.Order.instPreservesSupForallPointwise 4 := fun H =>
  absurd (H (R := Unit) (EPosts := Prop) (fun _ _ => True) () (ε := Unit))
    (not_ps_of _ (fun _ : Unit => False) (fun _ h => h () trivial))

-- `Lean.Order.instPreservesSupProdProd`: opA = const True, opB = id on `Prop`.
theorem instPreservesSupProdProd_7 : ¬ drop0% Lean.Order.instPreservesSupProdProd 7 := fun H =>
  absurd (H (R := Unit) (EPosts := Prop) (B := Prop) (fun _ _ => True) (fun _ => id) ())
    (not_ps_of _ (False, False) (fun _ h => h.1 trivial))

-- `Lean.Order.instPreservesSupProdProd`: opA = id, opB = const True on `Prop`.
theorem instPreservesSupProdProd_8 : ¬ drop0% Lean.Order.instPreservesSupProdProd 8 := fun H =>
  absurd (H (R := Unit) (EPosts := Prop) (B := Prop) (fun _ => id) (fun _ _ => True) ())
    (not_ps_of _ (False, False) (fun _ h => h.2 trivial))

-- `Lean.Order.instFrameOpOfPreservesSup`: op = const True on `Prop`.
theorem instFrameOpOfPreservesSup_4 : ¬ drop0% Lean.Order.instFrameOpOfPreservesSup 4 := fun H =>
  not_ps_true (@FrameOp.preservesSup _ _ _ _ _ _ _
    (H (Pred := Prop) (R := Unit) (op := fun _ _ => True)) ())

-- `Lean.Order.instFrameOpForallPointwise`: op = const True on `Prop`.
theorem instFrameOpForallPointwise_8 : ¬ drop0% Lean.Order.instFrameOpForallPointwise 8 :=
  fun H => not_ps_true (@FrameOp.preservesSup _ _ _ _ _ _ _
    (H (Pred := Prop) (R := Unit) (op := fun _ _ => True) (EPosts := Prop) (ε := Unit)
      (opE := fun _ => id)) ())

-- `Lean.Order.instFrameOpProdProd`: op = opB = id, opA = const True on `Prop`.
theorem instFrameOpProdProd_10 : ¬ drop0% Lean.Order.instFrameOpProdProd 10 := fun H =>
  absurd (@FrameOp.preservesSupE _ _ _ _ _ _ _
      (H (Pred := Prop) (R := Unit) (op := fun _ => id) (EPosts := Prop) (B := Prop)
        (opA := fun _ _ => True) (opB := fun _ => id)) ())
    (not_ps_of _ (False, False) (fun _ h => h.1 trivial))

-- `Lean.Order.instFrameOpProdProd`: op = opA = id, opB = const True on `Prop`.
theorem instFrameOpProdProd_11 : ¬ drop0% Lean.Order.instFrameOpProdProd 11 := fun H =>
  absurd (@FrameOp.preservesSupE _ _ _ _ _ _ _
      (H (Pred := Prop) (R := Unit) (op := fun _ => id) (EPosts := Prop) (B := Prop)
        (opA := fun _ => id) (opB := fun _ _ => True)) ())
    (not_ps_of _ (False, False) (fun _ h => h.2 trivial))

-- `Lean.Order.instFrameOpIgnoreOfPreservesSup`: op = const True on `Prop`.
theorem instFrameOpIgnoreOfPreservesSup_6 :
    ¬ drop0% Lean.Order.instFrameOpIgnoreOfPreservesSup 6 := fun H =>
  not_ps_true (@FrameOp.preservesSup _ _ _ _ _ _ _
    (H (Pred := Prop) (R := Unit) (op := fun _ _ => True) (EPosts := Prop)) ())

-- `Lean.Order.FrameOp.upperAdjoint_pointwise_apply`: as for
-- `Lean.Order.PreservesSup.upperAdjoint_comp_apply` (opE = const True, X b = (b = true)).
theorem FrameOp_upperAdjoint_pointwise_apply_5 :
    ¬ drop0% Lean.Order.FrameOp.upperAdjoint_pointwise_apply 5 := fun H => by
  have h1 : True ⊑ PreservesSup.upperAdjoint ((fun (_ : Unit) (_ : Prop) => True) ())
      ((fun b : Bool => b = true) true) :=
    PreservesSup.le_upperAdjoint _ (fun _ => rfl)
  have h2 : PreservesSup.upperAdjoint (FrameOp.pointwise (fun (_ : Unit) (_ : Prop) => True) ())
      (fun b : Bool => b = true) ⊑ fun _ => False :=
    ua_le _ _ _ fun Y hY => absurd (hY false trivial) Bool.false_ne_true
  have h3 := h2 true
  rw [H (A := Prop) (fun (_ : Unit) (_ : Prop) => True) () (fun b : Bool => b = true) true] at h3
  exact h3 (h1 trivial)

-- `Lean.Order.FrameOp.upperAdjoint_prod_fst`: removable, as for
-- `Lean.Order.PreservesSup.upperAdjoint_prodMap_fst` (only `opB r ⊥ = ⊥` is needed).
theorem FrameOp_upperAdjoint_prod_fst_7 : drop% Lean.Order.FrameOp.upperAdjoint_prod_fst 7 :=
  fun {_ _ _} _ _ opA opB hB r E => prodMap_fst' (opA r) (opB r) E

-- `Lean.Order.FrameOp.upperAdjoint_prod_fst`: opA = id, opB = const True on `Prop`,
-- E = (True, False).
theorem FrameOp_upperAdjoint_prod_fst_8 : ¬ drop0% Lean.Order.FrameOp.upperAdjoint_prod_fst 8 :=
  fun H => by
    have h := H (A := Prop) (B := Prop) (R := Unit) (fun _ => id) (fun _ _ => True) () (True, False)
    have h1 : True ⊑ PreservesSup.upperAdjoint ((fun (_ : Unit) => (id : Prop → Prop)) ())
        (True, False).fst := PreservesSup.le_upperAdjoint _ id
    have h2 : PreservesSup.upperAdjoint
        (FrameOp.prod (fun (_ : Unit) => (id : Prop → Prop)) (fun _ (_ : Prop) => True) ())
        (True, False) ⊑ (False, False) :=
      ua_le _ _ _ fun _ hx => (hx.2 trivial).elim
    have h3 := h2.1; rw [h] at h3; exact h3 (h1 trivial)

-- `Lean.Order.FrameOp.upperAdjoint_prod_snd`: opA = const True, opB = id on `Prop`,
-- E = (False, True).
theorem FrameOp_upperAdjoint_prod_snd_7 : ¬ drop0% Lean.Order.FrameOp.upperAdjoint_prod_snd 7 :=
  fun H => by
    have h := H (A := Prop) (B := Prop) (R := Unit) (fun _ _ => True) (fun _ => id) () (False, True)
    have h1 : True ⊑ PreservesSup.upperAdjoint ((fun (_ : Unit) => (id : Prop → Prop)) ())
        (False, True).snd := PreservesSup.le_upperAdjoint _ id
    have h2 : PreservesSup.upperAdjoint
        (FrameOp.prod (fun _ (_ : Prop) => True) (fun (_ : Unit) => (id : Prop → Prop)) ())
        (False, True) ⊑ (False, False) :=
      ua_le _ _ _ fun _ hx => (hx.1 trivial).elim
    have h3 := h2.2; rw [h] at h3; exact h3 (h1 trivial)

-- `Lean.Order.FrameOp.upperAdjoint_prod_snd`: removable, symmetric to
-- `Lean.Order.FrameOp.upperAdjoint_prod_fst` (only `opA r ⊥ = ⊥` is needed).
theorem FrameOp_upperAdjoint_prod_snd_8 : drop% Lean.Order.FrameOp.upperAdjoint_prod_snd 8 :=
  fun {_ _ _} _ _ opA opB hA r E => prodMap_snd' (opA r) (opB r) E

-- `Lean.Order.PredTrans.apply_frameClosure`: dependent; op = const True on `Prop` is no frame
-- operator.
theorem PredTrans_apply_frameClosure_8 : ¬ indep0% Lean.Order.PredTrans.apply_frameClosure 8 :=
  fun H => not_ps_true (@FrameOp.preservesSup _ _ _ _ _ _ _
    (H (Pred := Prop) (EPosts := Prop) (β := Unit) (R := Unit) (opE := fun _ => id)
      (fun _ _ => True) ⟨fun _ _ => True⟩ (fun _ => True) True) ())

-- `Lean.Order.PredTrans.monotone_frameClosure`: dependent; op = const True, t = const True
-- (monotone).
theorem PredTrans_monotone_frameClosure_8 :
    ¬ indep0% Lean.Order.PredTrans.monotone_frameClosure 8 := fun H =>
  not_ps_true (@FrameOp.preservesSup _ _ _ _ _ _ _
    (H (Pred := Prop) (EPosts := Prop) (β := Unit) (R := Unit) (opE := fun _ => id)
      (fun _ _ => True) (t := ⟨fun _ _ => True⟩) (fun _ _ _ _ _ _ h => h)) ())

-- `Lean.Order.PredTrans.monotone_frameClosure`: op = opE = id over one resource, so the closure
-- of the antitone t Q _ = ¬ Q () is t itself.
theorem PredTrans_monotone_frameClosure_10 :
    ¬ drop0% Lean.Order.PredTrans.monotone_frameClosure 10 := fun H => by
  let t : PredTrans Prop Prop Unit := ⟨fun Q _ => ¬ Q ()⟩
  have hm := H (Pred := Prop) (EPosts := Prop) (β := Unit) (R := Unit) (opE := fun _ => id)
    (fun _ => id) (t := t) (fun _ => False) (fun _ => True) True True id (fun _ _ => trivial)
  have lo : True ⊑ (t.frameClosure (fun (_ : Unit) => (id : Prop → Prop))).apply (fun _ => False) True :=
    (PredTrans.le_frameClosure_iff _ t).2 fun _ _ h => h
  have hi : (t.frameClosure (fun (_ : Unit) => (id : Prop → Prop))).apply (fun _ => True) True ⊑ ¬ True :=
    fc_le _ t _ _ () _ fun _ hx => hx
  exact hi (hm (lo trivial)) trivial

-- `Lean.Order.PredTrans.frameClosure_frames`: dependent; op = const True, comp trivial, both
-- action laws hold by `rfl`.
theorem PredTrans_frameClosure_frames_8 :
    ¬ indep0% Lean.Order.PredTrans.frameClosure_frames 8 := fun H =>
  not_ps_true (@FrameOp.preservesSup _ _ _ _ _ _ _
    (H (Pred := Prop) (EPosts := Prop) (β := Unit) (R := Unit) (opE := fun _ => id)
      (fun _ _ => True) (fun _ _ => ()) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      ⟨fun _ _ => True⟩ (fun _ => True) True ()) ())

-- `Lean.Order.PredTrans.frameClosure_frames`: Pred = Bool → Prop, one resource acting by the
-- swap `sw` (sw ∘ sw ≠ sw), opE = id; t Q _ = const (Q () true), Q () b = (b = false).
theorem PredTrans_frameClosure_frames_10 :
    ¬ drop0% Lean.Order.PredTrans.frameClosure_frames 10 := fun H => by
  haveI := mkFO (EPosts := Prop) (fun (_ : Unit) => sw) (fun _ => id) (fun _ => ps_sw) (fun _ => ps_id)
  let t : PredTrans (Bool → Prop) Prop Unit := ⟨fun Q _ => fun _ => Q () true⟩
  let Q0 : Unit → Bool → Prop := fun _ b => b = false
  have h := H (Pred := Bool → Prop) (EPosts := Prop) (β := Unit) (R := Unit) (opE := fun _ => id)
    (fun _ => sw) (fun _ _ => ()) (fun _ _ _ => rfl) t Q0 True ()
  have lo : (fun _ => True) ⊑ (t.frameClosure (fun (_ : Unit) => sw)).apply Q0 True :=
    (PredTrans.le_frameClosure_iff _ t).2 fun _ _ _ => rfl
  have hi : (t.frameClosure (fun (_ : Unit) => sw)).apply (fun a => sw (Q0 a)) True ⊑ fun _ => False :=
    fc_le _ t _ _ () _ fun x hx b hb =>
      absurd (hx (!b) (by simp only [sw, Bool.not_not]; exact hb)) Bool.noConfusion
  exact hi true (h true (sw_mono lo true trivial))

-- `Lean.Order.PredTrans.frameClosure_frames`: EPosts = Bool → Prop, opE acting by the swap `sw`,
-- op = id; t _ E = E true, E b = (b = false).
theorem PredTrans_frameClosure_frames_11 :
    ¬ drop0% Lean.Order.PredTrans.frameClosure_frames 11 := fun H => by
  haveI := mkFO (fun (_ : Unit) => (id : Prop → Prop)) (fun _ => sw) (fun _ => ps_id) (fun _ => ps_sw)
  let t : PredTrans Prop (Bool → Prop) Unit := ⟨fun _ E => E true⟩
  let E0 : Bool → Prop := fun b => b = false
  have h := H (Pred := Prop) (EPosts := Bool → Prop) (β := Unit) (R := Unit) (opE := fun _ => sw)
    (fun _ => id) (fun _ _ => ()) (fun _ _ _ => rfl) t (fun _ => True) E0 ()
  have lo : True ⊑ (t.frameClosure (fun (_ : Unit) => (id : Prop → Prop))).apply (fun _ => True) E0 :=
    (PredTrans.le_frameClosure_iff _ t).2 fun _ _ => rfl
  have hi : (t.frameClosure (fun (_ : Unit) => (id : Prop → Prop))).apply (fun a => id ((fun _ => True) a)) (sw E0) ⊑ False :=
    fc_le _ t _ _ () _ fun _ hx hxx => absurd (hx hxx : true = false) Bool.noConfusion
  exact hi (h (lo trivial))

-- `Lean.Order.PredTrans.le_frameClosure_iff`: dependent; op = const True.
theorem PredTrans_le_frameClosure_iff_8 :
    ¬ indep0% Lean.Order.PredTrans.le_frameClosure_iff 8 := fun H =>
  not_ps_true (@FrameOp.preservesSup _ _ _ _ _ _ _
    (H (Pred := Prop) (EPosts := Prop) (β := Unit) (R := Unit) (opE := fun _ => id)
      (fun _ _ => True) ⟨fun _ _ => True⟩ (Q := fun _ => True) (E := True) (pre := True)) ())

-- `Lean.Order.PredTrans.le_frameClosure`: dependent; op = const True, t = const True (both
-- premises hold).
theorem PredTrans_le_frameClosure_8 : ¬ indep0% Lean.Order.PredTrans.le_frameClosure 8 := fun H =>
  not_ps_true (@FrameOp.preservesSup _ _ _ _ _ _ _
    (H (Pred := Prop) (EPosts := Prop) (β := Unit) (R := Unit) (opE := fun _ => id)
      (fun _ _ => True) ⟨fun _ _ => True⟩ (Q := fun _ => True) (E := True) (pre := True)
      (fun _ _ _ => trivial) (fun _ => trivial)) ())

-- `Lean.Order.PredTrans.le_frameClosure`: op = id, opE = const False, t _ E = E, E = pre = True:
-- the closure is t at opE E = False.
theorem PredTrans_le_frameClosure_13 : ¬ drop0% Lean.Order.PredTrans.le_frameClosure 13 :=
  fun H => by
    haveI := mkFO (fun (_ : Unit) => (id : Prop → Prop)) (fun _ _ => False) (fun _ => ps_id)
      (fun _ => ps_false)
    let t : PredTrans Prop Prop Unit := ⟨fun _ E => E⟩
    have h := H (Pred := Prop) (EPosts := Prop) (β := Unit) (R := Unit) (opE := fun _ _ => False)
      (fun _ => id) t (Q := fun _ => True) (E := True) (pre := True) id
    have hi : (t.frameClosure (fun (_ : Unit) => (id : Prop → Prop))).apply (fun _ => True) True ⊑ False :=
      fc_le _ t _ _ () _ fun _ hx => hx
    exact hi (h trivial)

-- `Lean.Order.PredTrans.le_frameClosure`: op = opE = id, t = const False, pre = True.
theorem PredTrans_le_frameClosure_14 : ¬ drop0% Lean.Order.PredTrans.le_frameClosure 14 :=
  fun H => by
    let t : PredTrans Prop Prop Unit := ⟨fun _ _ => False⟩
    have h := H (Pred := Prop) (EPosts := Prop) (β := Unit) (R := Unit) (opE := fun _ => id)
      (fun _ => id) t (Q := fun _ => True) (E := True) (pre := True) (fun _ _ h => h)
    have hi : (t.frameClosure (fun (_ : Unit) => (id : Prop → Prop))).apply (fun _ => True) True ⊑ False :=
      fc_le _ t _ _ () _ fun _ hx => hx
    exact hi (h trivial)

-- `Lean.Order.PredTrans.frameClosure_le`: dependent; R = Bool, op false = id (the unit e),
-- op true = const True, opE = id.
theorem PredTrans_frameClosure_le_8 : ¬ indep0% Lean.Order.PredTrans.frameClosure_le 8 := fun H =>
  not_ps_true (@FrameOp.preservesSup _ _ _ _ _ _ _
    (H (Pred := Prop) (EPosts := Prop) (β := Unit) (R := Bool) (opE := fun _ => id)
      (fun b => Bool.rec (motive := fun _ => Prop → Prop) id (fun _ => True) b) false
      (fun _ => rfl) (fun _ => rfl) ⟨fun _ _ => True⟩ (fun _ => True) True) true)

-- `Lean.Order.PredTrans.frameClosure_le`: op = const False (not the identity at e), opE = id,
-- t = const False: the closure is `True`.
theorem PredTrans_frameClosure_le_10 : ¬ drop0% Lean.Order.PredTrans.frameClosure_le 10 :=
  fun H => by
    haveI := mkFO (fun (_ : Unit) (_ : Prop) => False) (fun _ => (id : Prop → Prop))
      (fun _ => ps_false) (fun _ => ps_id)
    let t : PredTrans Prop Prop Unit := ⟨fun _ _ => False⟩
    have h := H (Pred := Prop) (EPosts := Prop) (β := Unit) (R := Unit) (opE := fun _ => id)
      (fun _ _ => False) () (fun _ => rfl) t (fun _ => True) True
    have lo : True ⊑ (t.frameClosure (fun (_ : Unit) (_ : Prop) => False)).apply (fun _ => True) True :=
      (PredTrans.le_frameClosure_iff _ t).2 fun _ h => h
    exact h (lo trivial)

-- `Lean.Order.PredTrans.frameClosure_le`: op = id, opE = sw on EPosts = Bool → Prop,
-- t _ E = E true, E b = (b = false).
theorem PredTrans_frameClosure_le_11 : ¬ drop0% Lean.Order.PredTrans.frameClosure_le 11 :=
  fun H => by
    haveI := mkFO (fun (_ : Unit) => (id : Prop → Prop)) (fun _ => sw) (fun _ => ps_id)
      (fun _ => ps_sw)
    let t : PredTrans Prop (Bool → Prop) Unit := ⟨fun _ E => E true⟩
    let E0 : Bool → Prop := fun b => b = false
    have h := H (Pred := Prop) (EPosts := Bool → Prop) (β := Unit) (R := Unit) (opE := fun _ => sw)
      (fun _ => id) () (fun _ => rfl) t (fun _ => True) E0
    have lo : True ⊑ (t.frameClosure (fun (_ : Unit) => (id : Prop → Prop))).apply (fun _ => True) E0 :=
      (PredTrans.le_frameClosure_iff _ t).2 fun _ _ => rfl
    exact absurd (h (lo trivial)) Bool.noConfusion

end OrderHand
