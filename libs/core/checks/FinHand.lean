import Lean

/-!
Hand resolution of the 37 hypotheses in `Init.Data.Fin.Lemmas`, `Init.Data.Fin.Fold` and
`Init.Data.Fin.Iterate` that `HypCheck.lean` left unresolved. For each hypothesis `hᵢ` of theorem
`T`, this file proves either `T'` (the theorem without `hᵢ`: removable) or `¬T'` (necessary). For
dependent hypotheses (`[NeZero n]`, `Fin.cases_succ'`'s `h`) removability means `∀ indep, Hᵢ`
(proved as `FinHand.*_inst`, followed by the restated theorem) and necessity means
`¬ ∀ indep, Hᵢ` (see `Methods.md`). Universe-polymorphic statements are refuted at one fixed
universe (`Type → Type` for the monad, `Type` for `hIterate_eq`'s `P`) or at all universes.

`Fin.foldrM.loop` is private and its equations are not reachable through any public lemma
without `LawfulMonad`; `foldPriv%` refers to private declarations of `Init.Data.Fin.Fold`, hence
`import Lean`.

Run with the lean4 repo's stage1 binary: `lean checks/FinHand.lean`.
-/

set_option linter.unusedVariables false
set_option warn.classDefReducibility false

open Lean Meta Elab Term in
/-- The private declaration `id` of `Init.Data.Fin.Fold`. -/
elab "foldPriv% " id:ident : term => do
  let n := mkPrivateNameCore `Init.Data.Fin.Fold id.getId
  let c ← getConstInfo n
  return mkConst n (← c.levelParams.mapM fun _ => mkFreshLevelMVar)

namespace FinHand

theorem neZero_of_fin {n : Nat} (i : Fin n) : NeZero n := ⟨by have := i.isLt; omega⟩

/-- Bind-counting monad: `pure` has count 0, every `bind` adds 1. -/
def countM : Monad (fun α => Nat × α) :=
  { pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) }

/-- `bind` keeps the counter of its first argument: `x >>= pure = x`, but
`pure a >>= f = (0, (f a).2)`, so `pure` is not a left unit. -/
def firstM : Monad (fun α => Nat × α) :=
  { pure := fun a => (0, a), bind := fun x f => (x.1, (f x.2).2) }

theorem foldrM_loop_castSucc {m : Type u → Type v} [Monad m] {α : Type u} {n : Nat}
    (f : Fin (n + 1) → α → m α) : ∀ (i : Nat) (h : i ≤ n) (h' : i ≤ n + 1) (x : α),
    (foldPriv% Fin.foldrM.loop) (n + 1) f ⟨i, h'⟩ x =
      (foldPriv% Fin.foldrM.loop) n (fun j => f j.castSucc) ⟨i, h⟩ x
  | 0, _, _, x => by rw [foldPriv% Fin.foldrM.loop.eq_1, foldPriv% Fin.foldrM.loop.eq_1]
  | i + 1, h, h', x => by
    rw [foldPriv% Fin.foldrM.loop.eq_2, foldPriv% Fin.foldrM.loop.eq_2]
    congr 1
    funext y
    exact foldrM_loop_castSucc f i _ _ y

/-- `foldrM 1` without `LawfulMonad`. -/
theorem foldrM_one {m : Type u → Type v} [Monad m] {α : Type u} (f : Fin 1 → α → m α) (x : α) :
    Fin.foldrM 1 f x = f 0 x >>= pure := by
  unfold Fin.foldrM
  rw [foldPriv% Fin.foldrM.loop.eq_2]
  congr 1
  funext y
  rw [foldPriv% Fin.foldrM.loop.eq_1]

end FinHand

/-! ## Removable (27) -/

-- `Fin.foldrM_succ_last` (`[LawfulMonad m]`): the right-to-left loop over `Fin (n+1)` first
-- applies `f (last n)` and then runs exactly the loop over `Fin n`; no monad law is used.
theorem FinHand.foldrM_succ_last {m : Type u → Type v} {n : Nat} {α : Type u} [Monad m]
    (f : Fin (n + 1) → α → m α) :
    Fin.foldrM (n + 1) f = fun x => f (Fin.last n) x >>= Fin.foldrM n fun i => f i.castSucc := by
  funext x
  unfold Fin.foldrM
  rw [foldPriv% Fin.foldrM.loop.eq_2]
  congr 1
  funext y
  exact FinHand.foldrM_loop_castSucc f n _ _ y

-- The 26 `[NeZero n]` instances below are dependent (used to build `0`, `1`, `Fin.ofNat n`, …)
-- and each theorem has an independent parameter `_ : Fin n` (or `ha : a < n`), so `n ≠ 0`.

-- `Fin.zero_eq_mk` (`[NeZero n]`, dependent): derivable from `ha : a < n`.
theorem FinHand.zero_eq_mk_inst {n a : Nat} (ha : a < n) : NeZero n := ⟨by omega⟩
theorem FinHand.zero_eq_mk {n a : Nat} {ha : a < n} :
    haveI := FinHand.zero_eq_mk_inst ha; 0 = (⟨a, ha⟩ : Fin n) ↔ a = 0 :=
  @Fin.zero_eq_mk n a ha (FinHand.zero_eq_mk_inst ha)

-- `Fin.mk_eq_zero` (`[NeZero n]`, dependent): derivable from `ha : a < n`.
theorem FinHand.mk_eq_zero_inst {n a : Nat} (ha : a < n) : NeZero n := ⟨by omega⟩
theorem FinHand.mk_eq_zero {n a : Nat} {ha : a < n} :
    haveI := FinHand.mk_eq_zero_inst ha; (⟨a, ha⟩ : Fin n) = 0 ↔ a = 0 :=
  @Fin.mk_eq_zero n a ha (FinHand.mk_eq_zero_inst ha)

-- `Fin.sub_ofNat` (`[NeZero n]`, dependent): derivable from `x : Fin n`.
theorem FinHand.sub_ofNat_inst {n : Nat} (x : Fin n) (y : Nat) : NeZero n := FinHand.neZero_of_fin x
theorem FinHand.sub_ofNat {n : Nat} (x : Fin n) (y : Nat) :
    haveI := FinHand.sub_ofNat_inst x y; x - Fin.ofNat n y = Fin.ofNat n (n - y % n + x.val) :=
  @Fin.sub_ofNat n (FinHand.sub_ofNat_inst x y) x y

-- `Fin.mul_ofNat` (`[NeZero n]`, dependent): derivable from `x : Fin n`.
theorem FinHand.mul_ofNat_inst {n : Nat} (x : Fin n) (y : Nat) : NeZero n := FinHand.neZero_of_fin x
theorem FinHand.mul_ofNat {n : Nat} (x : Fin n) (y : Nat) :
    haveI := FinHand.mul_ofNat_inst x y; x * Fin.ofNat n y = Fin.ofNat n (x.val * y) :=
  @Fin.mul_ofNat n (FinHand.mul_ofNat_inst x y) x y

-- `Fin.ofNat_sub` (`[NeZero n]`, dependent): derivable from `y : Fin n`.
theorem FinHand.ofNat_sub_inst {n : Nat} (x : Nat) (y : Fin n) : NeZero n := FinHand.neZero_of_fin y
theorem FinHand.ofNat_sub {n : Nat} (x : Nat) (y : Fin n) :
    haveI := FinHand.ofNat_sub_inst x y; Fin.ofNat n x - y = Fin.ofNat n (n - y.val + x) :=
  @Fin.ofNat_sub n (FinHand.ofNat_sub_inst x y) x y

-- `Fin.ofNat_mul` (`[NeZero n]`, dependent): derivable from `y : Fin n`.
theorem FinHand.ofNat_mul_inst {n : Nat} (x : Nat) (y : Fin n) : NeZero n := FinHand.neZero_of_fin y
theorem FinHand.ofNat_mul {n : Nat} (x : Nat) (y : Fin n) :
    haveI := FinHand.ofNat_mul_inst x y; Fin.ofNat n x * y = Fin.ofNat n (x * y.val) :=
  @Fin.ofNat_mul n (FinHand.ofNat_mul_inst x y) x y

-- `Fin.add_ofNat` (`[NeZero n]`, dependent): derivable from `x : Fin n`.
theorem FinHand.add_ofNat_inst {n : Nat} (x : Fin n) (y : Nat) : NeZero n := FinHand.neZero_of_fin x
theorem FinHand.add_ofNat {n : Nat} (x : Fin n) (y : Nat) :
    haveI := FinHand.add_ofNat_inst x y; x + Fin.ofNat n y = Fin.ofNat n (x.val + y) :=
  @Fin.add_ofNat n (FinHand.add_ofNat_inst x y) x y

-- `Fin.ofNat_add` (`[NeZero n]`, dependent): derivable from `y : Fin n`.
theorem FinHand.ofNat_add_inst {n : Nat} (x : Nat) (y : Fin n) : NeZero n := FinHand.neZero_of_fin y
theorem FinHand.ofNat_add {n : Nat} (x : Nat) (y : Fin n) :
    haveI := FinHand.ofNat_add_inst x y; Fin.ofNat n x + y = Fin.ofNat n (x + y.val) :=
  @Fin.ofNat_add n (FinHand.ofNat_add_inst x y) x y

-- `Fin.ofNat_val_eq_self` (`[NeZero n]`, dependent): derivable from `x : Fin n`.
theorem FinHand.ofNat_val_eq_self_inst {n : Nat} (x : Fin n) : NeZero n := FinHand.neZero_of_fin x
theorem FinHand.ofNat_val_eq_self {n : Nat} (x : Fin n) :
    haveI := FinHand.ofNat_val_eq_self_inst x; Fin.ofNat n x.val = x :=
  @Fin.ofNat_val_eq_self n (FinHand.ofNat_val_eq_self_inst x) x

-- `Fin.not_lt_zero` (`[NeZero n]`, dependent): derivable from `a : Fin n`.
theorem FinHand.not_lt_zero_inst {n : Nat} (a : Fin n) : NeZero n := FinHand.neZero_of_fin a
theorem FinHand.not_lt_zero {n : Nat} (a : Fin n) :
    haveI := FinHand.not_lt_zero_inst a; ¬a < 0 :=
  @Fin.not_lt_zero n (FinHand.not_lt_zero_inst a) a

-- `Fin.zero_le` (`[NeZero n]`, dependent): derivable from `a : Fin n`.
theorem FinHand.zero_le_inst {n : Nat} (a : Fin n) : NeZero n := FinHand.neZero_of_fin a
theorem FinHand.zero_le {n : Nat} (a : Fin n) :
    haveI := FinHand.zero_le_inst a; 0 ≤ a :=
  @Fin.zero_le n (FinHand.zero_le_inst a) a

-- `Fin.pos_iff_ne_zero` (`[NeZero n]`, dependent): derivable from `a : Fin n`.
theorem FinHand.pos_iff_ne_zero_inst {n : Nat} (a : Fin n) : NeZero n := FinHand.neZero_of_fin a
theorem FinHand.pos_iff_ne_zero {n : Nat} {a : Fin n} :
    haveI := FinHand.pos_iff_ne_zero_inst a; 0 < a ↔ a ≠ 0 :=
  @Fin.pos_iff_ne_zero n (FinHand.pos_iff_ne_zero_inst a) a

-- `Fin.val_eq_zero_iff` (`[NeZero n]`, dependent): derivable from `a : Fin n`.
theorem FinHand.val_eq_zero_iff_inst {n : Nat} (a : Fin n) : NeZero n := FinHand.neZero_of_fin a
theorem FinHand.val_eq_zero_iff {n : Nat} {a : Fin n} :
    haveI := FinHand.val_eq_zero_iff_inst a; a.val = 0 ↔ a = 0 :=
  @Fin.val_eq_zero_iff n (FinHand.val_eq_zero_iff_inst a) a

-- `Fin.val_ne_zero_iff` (`[NeZero n]`, dependent): derivable from `a : Fin n`.
theorem FinHand.val_ne_zero_iff_inst {n : Nat} (a : Fin n) : NeZero n := FinHand.neZero_of_fin a
theorem FinHand.val_ne_zero_iff {n : Nat} {a : Fin n} :
    haveI := FinHand.val_ne_zero_iff_inst a; a.val ≠ 0 ↔ a ≠ 0 :=
  @Fin.val_ne_zero_iff n (FinHand.val_ne_zero_iff_inst a) a

-- `Fin.castSucc_eq_zero_iff` (`[NeZero n]`, dependent): derivable from `a : Fin n`.
theorem FinHand.castSucc_eq_zero_iff_inst {n : Nat} (a : Fin n) : NeZero n := FinHand.neZero_of_fin a
theorem FinHand.castSucc_eq_zero_iff {n : Nat} {a : Fin n} :
    haveI := FinHand.castSucc_eq_zero_iff_inst a; a.castSucc = 0 ↔ a = 0 :=
  @Fin.castSucc_eq_zero_iff n (FinHand.castSucc_eq_zero_iff_inst a) a

-- `Fin.castSucc_ne_zero_iff` (`[NeZero n]`, dependent): derivable from `a : Fin n`.
theorem FinHand.castSucc_ne_zero_iff_inst {n : Nat} (a : Fin n) : NeZero n := FinHand.neZero_of_fin a
theorem FinHand.castSucc_ne_zero_iff {n : Nat} {a : Fin n} :
    haveI := FinHand.castSucc_ne_zero_iff_inst a; a.castSucc ≠ 0 ↔ a ≠ 0 :=
  @Fin.castSucc_ne_zero_iff n (FinHand.castSucc_ne_zero_iff_inst a) a

-- `Fin.castSucc_pos` (`[NeZero n]`, dependent): derivable from `i : Fin n`.
theorem FinHand.castSucc_pos_inst {n : Nat} (i : Fin n) : NeZero n := FinHand.neZero_of_fin i
theorem FinHand.castSucc_pos {n : Nat} {i : Fin n} :
    haveI := FinHand.castSucc_pos_inst i; 0 < i → 0 < i.castSucc :=
  @Fin.castSucc_pos n (FinHand.castSucc_pos_inst i) i

-- `Fin.zero_add` (`[NeZero n]`, dependent): derivable from `k : Fin n`.
theorem FinHand.zero_add_inst {n : Nat} (k : Fin n) : NeZero n := FinHand.neZero_of_fin k
theorem FinHand.zero_add {n : Nat} (k : Fin n) :
    haveI := FinHand.zero_add_inst k; 0 + k = k :=
  @Fin.zero_add n (FinHand.zero_add_inst k) k

-- `Fin.add_zero` (`[NeZero n]`, dependent): derivable from `k : Fin n`.
theorem FinHand.add_zero_inst {n : Nat} (k : Fin n) : NeZero n := FinHand.neZero_of_fin k
theorem FinHand.add_zero {n : Nat} (k : Fin n) :
    haveI := FinHand.add_zero_inst k; k + 0 = k :=
  @Fin.add_zero n (FinHand.add_zero_inst k) k

-- `Fin.zero_mul` (`[NeZero n]`, dependent): derivable from `k : Fin n`.
theorem FinHand.zero_mul_inst {n : Nat} (k : Fin n) : NeZero n := FinHand.neZero_of_fin k
theorem FinHand.zero_mul {n : Nat} (k : Fin n) :
    haveI := FinHand.zero_mul_inst k; 0 * k = 0 :=
  @Fin.zero_mul n (FinHand.zero_mul_inst k) k

-- `Fin.mul_zero` (`[NeZero n]`, dependent): derivable from `k : Fin n`.
theorem FinHand.mul_zero_inst {n : Nat} (k : Fin n) : NeZero n := FinHand.neZero_of_fin k
theorem FinHand.mul_zero {n : Nat} (k : Fin n) :
    haveI := FinHand.mul_zero_inst k; k * 0 = 0 :=
  @Fin.mul_zero n (FinHand.mul_zero_inst k) k

-- `Fin.one_mul` (`[NeZero n]`, dependent): derivable from `k : Fin n`.
theorem FinHand.one_mul_inst {n : Nat} (k : Fin n) : NeZero n := FinHand.neZero_of_fin k
theorem FinHand.one_mul {n : Nat} (k : Fin n) :
    haveI := FinHand.one_mul_inst k; 1 * k = k :=
  @Fin.one_mul n (FinHand.one_mul_inst k) k

-- `Fin.mul_one` (`[NeZero n]`, dependent): derivable from `k : Fin n`.
theorem FinHand.mul_one_inst {n : Nat} (k : Fin n) : NeZero n := FinHand.neZero_of_fin k
theorem FinHand.mul_one {n : Nat} (k : Fin n) :
    haveI := FinHand.mul_one_inst k; k * 1 = k :=
  @Fin.mul_one n (FinHand.mul_one_inst k) k

-- `Fin.pow_zero` (`[NeZero n]`, dependent): derivable from `a : Fin n`.
theorem FinHand.pow_zero_inst {n : Nat} (a : Fin n) : NeZero n := FinHand.neZero_of_fin a
theorem FinHand.pow_zero {n : Nat} (a : Fin n) :
    haveI := FinHand.pow_zero_inst a; a ^ 0 = 1 :=
  @Fin.pow_zero n (FinHand.pow_zero_inst a) a

-- `Fin.sub_self` (`[NeZero n]`, dependent): derivable from `x : Fin n`.
theorem FinHand.sub_self_inst {n : Nat} (x : Fin n) : NeZero n := FinHand.neZero_of_fin x
theorem FinHand.sub_self {n : Nat} {x : Fin n} :
    haveI := FinHand.sub_self_inst x; x - x = 0 :=
  @Fin.sub_self n (FinHand.sub_self_inst x) x

-- `Fin.val_neg` (`[NeZero n]`, dependent): derivable from `x : Fin n`.
theorem FinHand.val_neg_inst {n : Nat} (x : Fin n) : NeZero n := FinHand.neZero_of_fin x
theorem FinHand.val_neg {n : Nat} (x : Fin n) :
    haveI := FinHand.val_neg_inst x; (-x).val = if x = 0 then 0 else n - x.val :=
  @Fin.val_neg n (FinHand.val_neg_inst x) x
/-! ### Consistency: each restatement gives back the original theorem -/

example : type_of% @Fin.foldrM_succ_last := fun f => FinHand.foldrM_succ_last f
example : type_of% @Fin.zero_eq_mk := @fun n a ha _ => @FinHand.zero_eq_mk n a ha
example : type_of% @Fin.mk_eq_zero := @fun n a ha _ => @FinHand.mk_eq_zero n a ha
example : type_of% @Fin.sub_ofNat := @fun n _ => @FinHand.sub_ofNat n
example : type_of% @Fin.mul_ofNat := @fun n _ => @FinHand.mul_ofNat n
example : type_of% @Fin.ofNat_sub := @fun n _ => @FinHand.ofNat_sub n
example : type_of% @Fin.ofNat_mul := @fun n _ => @FinHand.ofNat_mul n
example : type_of% @Fin.add_ofNat := @fun n _ => @FinHand.add_ofNat n
example : type_of% @Fin.ofNat_add := @fun n _ => @FinHand.ofNat_add n
example : type_of% @Fin.ofNat_val_eq_self := @fun n _ => @FinHand.ofNat_val_eq_self n
example : type_of% @Fin.not_lt_zero := @fun n _ => @FinHand.not_lt_zero n
example : type_of% @Fin.zero_le := @fun n _ => @FinHand.zero_le n
example : type_of% @Fin.pos_iff_ne_zero := @fun n _ => @FinHand.pos_iff_ne_zero n
example : type_of% @Fin.val_eq_zero_iff := @fun n _ => @FinHand.val_eq_zero_iff n
example : type_of% @Fin.val_ne_zero_iff := @fun n _ => @FinHand.val_ne_zero_iff n
example : type_of% @Fin.castSucc_eq_zero_iff := @fun n _ => @FinHand.castSucc_eq_zero_iff n
example : type_of% @Fin.castSucc_ne_zero_iff := @fun n _ => @FinHand.castSucc_ne_zero_iff n
example : type_of% @Fin.castSucc_pos := @fun n _ => @FinHand.castSucc_pos n
example : type_of% @Fin.zero_add := @fun n _ => @FinHand.zero_add n
example : type_of% @Fin.add_zero := @fun n _ => @FinHand.add_zero n
example : type_of% @Fin.zero_mul := @fun n _ => @FinHand.zero_mul n
example : type_of% @Fin.mul_zero := @fun n _ => @FinHand.mul_zero n
example : type_of% @Fin.one_mul := @fun n _ => @FinHand.one_mul n
example : type_of% @Fin.mul_one := @fun n _ => @FinHand.mul_one n
example : type_of% @Fin.pow_zero := @fun n _ => @FinHand.pow_zero n
example : type_of% @Fin.sub_self := @fun n _ => @FinHand.sub_self n
example : type_of% @Fin.val_neg := @fun n _ => @FinHand.val_neg n

/-! ## Necessary (10) -/

/-! ### `Init.Data.Fin.Fold`: `[LawfulMonad m]` -/

-- `Fin.foldrM_add` (`[LawfulMonad m]`): `countM`, `n = k = 0`: `pure x` has count 0,
-- `pure x >>= pure` has count 1.
example : ¬ ∀ {m : Type → Type} {n k : Nat} {α : Type} [Monad m] (f : Fin (n + k) → α → m α),
    Fin.foldrM (n + k) f = fun x =>
      Fin.foldrM k (fun i => f (Fin.natAdd n i)) x >>=
        Fin.foldrM n fun i => f (Fin.castLE (Nat.le_add_right n k) i) := by
  intro h
  letI := FinHand.countM
  have := congrFun (@h (fun α => Nat × α) 0 0 Nat _ (fun _ x => (0, x))) 0
  rw [show Fin.foldrM (0 + 0) (fun _ x => (0, x)) 0 = pure 0 from congrFun (Fin.foldrM_zero _) 0,
    Fin.foldrM_zero] at this
  revert this; decide

-- `Fin.foldlM_add` (`[LawfulMonad m]`): `countM`, `n = k = 0`.
example : ¬ ∀ {m : Type → Type} {α : Type} {n k : Nat} [Monad m] (f : α → Fin (n + k) → m α),
    Fin.foldlM (n + k) f = fun x =>
      Fin.foldlM n (fun x i => f x (Fin.castLE (Nat.le_add_right n k) i)) x >>=
        Fin.foldlM k fun x i => f x (Fin.natAdd n i) := by
  intro h
  letI := FinHand.countM
  have := congrFun (@h (fun α => Nat × α) Nat 0 0 _ (fun x _ => (0, x))) 0
  rw [show Fin.foldlM (0 + 0) (fun x _ => (0, x)) 0 = pure 0 from congrFun (Fin.foldlM_zero _) 0,
    Fin.foldlM_zero] at this
  revert this; decide

-- `Fin.foldrM_pure` (`[LawfulMonad m]`): `countM`, `n = 1`: `pure (f 0 x) >>= pure` has count 1,
-- `pure _` has count 0.
example : ¬ ∀ {m : Type → Type} {α : Type} {x : α} [Monad m] {n : Nat} {f : Fin n → α → α},
    Fin.foldrM n (fun i x => (pure (f i x) : m α)) x = pure (Fin.foldr n f x) := by
  intro h
  letI := FinHand.countM
  have := @h (fun α => Nat × α) Nat 0 _ 1 (fun _ x => x)
  rw [FinHand.foldrM_one] at this
  revert this; decide

-- `Fin.foldrM_succ` (`[LawfulMonad m]`): `firstM`, `n = 0`, `f _ x = (1, x)`:
-- `f 0 0 >>= pure = (1, 0)` but `pure 0 >>= f 0 = (0, 0)`.
example : ¬ ∀ {m : Type → Type} {n : Nat} {α : Type} [Monad m] (f : Fin (n + 1) → α → m α),
    Fin.foldrM (n + 1) f = fun x => Fin.foldrM n (fun i => f i.succ) x >>= f 0 := by
  intro h
  letI := FinHand.firstM
  have := congrFun (@h (fun α => Nat × α) 0 Nat _ (fun _ x => (1, x))) 0
  rw [FinHand.foldrM_one, Fin.foldrM_zero] at this
  revert this; decide

-- `Fin.foldlM_succ_last` (`[LawfulMonad m]`): `firstM`, `n = 0`, `f x _ = (1, x)`.
example : ¬ ∀ {m : Type → Type} {α : Type} {n : Nat} [Monad m] (f : α → Fin (n + 1) → m α),
    Fin.foldlM (n + 1) f =
      fun x => Fin.foldlM n (fun x j => f x j.castSucc) x >>= fun x => f x (Fin.last n) := by
  intro h
  letI := FinHand.firstM
  have := congrFun (@h (fun α => Nat × α) Nat 0 _ (fun x _ => (1, x))) 0
  rw [Fin.foldlM_succ, Fin.foldlM_zero] at this
  revert this; decide

/-! ### `Init.Data.Fin.Iterate` -/

-- `hIterate_elim` is refuted at every universe. `hIterate_eq` is refuted at `P : Nat → Type`
-- (`u_1 := 1`); at `Sort 0` both its versions hold by proof irrelevance.

-- `Fin.hIterate_elim` (`init`): `Q := fun _ _ => False`, `n = 0` (so `step` is vacuous).
example : ¬ ∀ {P : Nat → Sort u} (Q : (i : Nat) → P i → Prop) {n : Nat}
    (f : (i : Fin n) → P i.val → P (i.val + 1)) (s : P 0),
    (∀ (k : Fin n) (s : P k.val), Q k.val s → Q (k.val + 1) (f k s)) → Q n (Fin.hIterate P s f) :=
  fun h => h (P := fun _ => PUnit) (fun _ _ => False) (n := 0) (fun _ _ => ⟨⟩) ⟨⟩ (fun k => k.elim0)

-- `Fin.hIterate_elim` (`step`): `Q i _ := i = 0`, `n = 1`.
example : ¬ ∀ {P : Nat → Sort u} (Q : (i : Nat) → P i → Prop) {n : Nat}
    (f : (i : Fin n) → P i.val → P (i.val + 1)) (s : P 0),
    Q 0 s → Q n (Fin.hIterate P s f) :=
  fun h => absurd (h (P := fun _ => PUnit) (fun i _ => i = 0) (n := 1) (fun _ _ => ⟨⟩) ⟨⟩ rfl)
    (by decide)

-- `Fin.hIterate_eq` (`init`): `P := fun _ => Nat`, `state := fun _ => 0`, `n = 0`, `s = 1`;
-- `hIterate` over `Fin 0` returns `s` (by `hIterate_elim`).
example : ¬ ∀ {P : Nat → Type} (state : (i : Nat) → P i) {n : Nat}
    (f : (i : Fin n) → P i.val → P (i.val + 1)) (s : P 0),
    (∀ (i : Fin n), f i (state i.val) = state (i.val + 1)) → Fin.hIterate P s f = state n := by
  intro h
  have h1 := h (P := fun _ => Nat) (fun _ => 0) (n := 0) (fun _ x => x) 1 (fun i => i.elim0)
  have h2 := Fin.hIterate_elim (P := fun _ => Nat) (fun _ x => x = 1) (n := 0) (fun _ x => x) 1
    rfl (fun k => k.elim0)
  rw [h1] at h2
  cases h2

-- `Fin.hIterate_eq` (`step`): `P := fun _ => Nat`, `state := fun _ => 0`, `f _ x := x + 1`,
-- `n = 1`, `s = 0`; then `hIterate = 1` (by `hIterate_elim` with `Q i x := x = i`).
example : ¬ ∀ {P : Nat → Type} (state : (i : Nat) → P i) {n : Nat}
    (f : (i : Fin n) → P i.val → P (i.val + 1)) (s : P 0),
    s = state 0 → Fin.hIterate P s f = state n := by
  intro h
  have h1 := h (P := fun _ => Nat) (fun _ => 0) (n := 1) (fun _ x => x + 1) 0 rfl
  have h2 := Fin.hIterate_elim (P := fun _ => Nat) (fun i x => x = i) (n := 1) (fun _ x => x + 1) 0
    rfl (fun _ _ hs => congrArg (· + 1) hs)
  rw [h1] at h2
  cases h2

/-! ### `Init.Data.Fin.Lemmas` -/

-- `Fin.cases_succ'` (`h : i + 1 < n + 1`, dependent): independent parameters `n`, `motive`,
-- `zero`, `succ`, `i`; `n = i = 0` gives `1 < 1`.
example : ¬ ∀ {n : Nat} {motive : Fin (n + 1) → Sort u} {zero : motive 0}
    {succ : (i : Fin n) → motive i.succ} {i : Nat}, i + 1 < n + 1 :=
  fun h => absurd (h (n := 0) (motive := fun _ => PUnit) (zero := ⟨⟩) (succ := fun _ => ⟨⟩) (i := 0))
    (by decide)

#print axioms FinHand.foldrM_succ_last
#print axioms FinHand.val_neg
