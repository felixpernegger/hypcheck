module
public import HCHeaderM
import HCRefute
import all CombinatorialGames.Counterexamples.Multiplication
import all CombinatorialGames.Counterexamples.OrdinalSum
import all CombinatorialGames.Counterexamples.TinyOrder
import all CombinatorialGames.Game.Basic
import all CombinatorialGames.Game.Birthday
import all CombinatorialGames.Game.Canonical
import all CombinatorialGames.Game.Classes
import all CombinatorialGames.Game.Confusion
import all CombinatorialGames.Game.Functor
import all CombinatorialGames.Game.Graph
import all CombinatorialGames.Game.IGame
import all CombinatorialGames.Game.Impartial.Grundy
import all CombinatorialGames.Game.Impartial.Multiplication
import all CombinatorialGames.Game.Loopy.Basic
import all CombinatorialGames.Game.Loopy.IGame
import all CombinatorialGames.Game.Loopy.Outcome
import all CombinatorialGames.Game.Loopy.StoppingTime
import all CombinatorialGames.Game.Order
import all CombinatorialGames.Game.Ordinal
import all CombinatorialGames.Game.OrdinalSum
import all CombinatorialGames.Game.Player
import all CombinatorialGames.Game.Small
import all CombinatorialGames.Game.Special
import all CombinatorialGames.Game.Specific.Domineering
import all CombinatorialGames.Game.Specific.Nim
import all CombinatorialGames.Game.Specific.Poset
import all CombinatorialGames.Game.Stops
import all CombinatorialGames.Mathlib.Dyadic
import all CombinatorialGames.Mathlib.EtaSet
import all CombinatorialGames.Mathlib.SignType
import all CombinatorialGames.Mathlib.Small
import all CombinatorialGames.Mathlib.WithTop
import all CombinatorialGames.NatOrdinal.AddMonoidAlgebra
import all CombinatorialGames.NatOrdinal.Basic
import all CombinatorialGames.NatOrdinal.Pow
import all CombinatorialGames.Nimber.Basic
import all CombinatorialGames.Nimber.Field
import all CombinatorialGames.Nimber.Nat
import all CombinatorialGames.Nimber.NatOrdinal
import all CombinatorialGames.Nimber.Omega
import all CombinatorialGames.Nimber.SimplestExtension.Algebraic
import all CombinatorialGames.Nimber.SimplestExtension.Basic
import all CombinatorialGames.Nimber.SimplestExtension.Closure
import all CombinatorialGames.Nimber.SimplestExtension.Polynomial
import all CombinatorialGames.Nimber.SmallDegree.Inseparable
import all CombinatorialGames.Nimber.SmallDegree.Quartic
import all CombinatorialGames.SignExpansion.Basic
import all CombinatorialGames.SignExpansion.Simplicity
import all CombinatorialGames.SignExpansion.Surreal
import all CombinatorialGames.Surreal.Basic
import all CombinatorialGames.Surreal.Birthday.Basic
import all CombinatorialGames.Surreal.Birthday.Cut
import all CombinatorialGames.Surreal.Birthday.Dyadic
import all CombinatorialGames.Surreal.Cut
import all CombinatorialGames.Surreal.Division
import all CombinatorialGames.Surreal.Dyadic
import all CombinatorialGames.Surreal.HahnSeries.Basic
import all CombinatorialGames.Surreal.Leading
import all CombinatorialGames.Surreal.Multiplication
import all CombinatorialGames.Surreal.Omnific.Basic
import all CombinatorialGames.Surreal.Ordinal
import all CombinatorialGames.Surreal.Pow
import all CombinatorialGames.Surreal.Real
import all CombinatorialGames.Tactic.AddInstances
import all CombinatorialGames.Tactic.GameCmp
import all CombinatorialGames.Tactic.OrdinalAlias
import all CombinatorialGames.Tactic.Register
import all CombinatorialGames.Test.GameCmp

namespace T2c0
open IGame Set

-- helper: W = {up |} ≈ 1 but not numeric, W * ½ ≈ 1

noncomputable abbrev W : IGame := !{{IGame.up} | ∅}
noncomputable abbrev TH : IGame := !{{1} | {2}}
noncomputable abbrev SF : IGame := !{{TH} | {2}}
noncomputable abbrev Q : IGame := !{{½} | {1}}

set_option maxHeartbeats 3000000 in
theorem wHalf : W * ½ ≈ 1 := by game_cmp

set_option maxHeartbeats 3000000 in
theorem thHalf : TH * ½ ≈ Q := by game_cmp

set_option maxHeartbeats 3000000 in
theorem qsf : Q + SF - TH ≈ 1 := by game_cmp

instance numTH : Numeric TH := by
  apply Numeric.mk <;> simp <;> first | game_cmp | infer_instance

instance numSF : Numeric SF := by
  apply Numeric.mk <;> simp <;> first | game_cmp | exact ⟨numTH, inferInstance⟩ | infer_instance

-- helper: IH1 holds for numeric games
theorem ih1Num {x y : IGame} [hx : Numeric x] [hy : Numeric y] :
    (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».IH1) x y := by
  intro p q a b y' ha hb hy'
  have : Numeric a := Numeric.of_mem_moves ha
  have : Numeric b := Numeric.of_mem_moves hb
  have : Numeric y' := by
    rcases hy' with rfl | ⟨u, hu⟩
    · exact hy
    · exact Numeric.of_mem_moves hu
  exact (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».main_P24) a b y'

-- helper: the key failure: W·½ + SF·0 − W·0 is not below −(TH·(−½) + SF·(−1) − TH·(−1))
theorem key10 : ¬ Game.mk (mulOption SF ½ W 0) < -Game.mk (mulOption SF (-½) TH (-1)) := by
  rw [Game.mk_mulOption, Game.mk_mulOption]
  simp only [mul_zero, mul_neg, mul_one, Game.mk_zero, Game.mk_neg, add_zero, sub_zero]
  rw [Game.mk_eq wHalf, Game.mk_eq thHalf]
  have e := Game.mk_eq qsf
  simp only [Game.mk_sub, Game.mk_add, Game.mk_one] at e
  intro hlt
  have : (1 : Game) < 1 := by
    calc (1 : Game) < -(-Game.mk Q + -Game.mk SF - -Game.mk TH) := hlt
      _ = Game.mk Q + Game.mk SF - Game.mk TH := by abel
      _ = 1 := e
  exact lt_irrefl _ this


-- helper: XW = {W, 3/2 | 2} is equivalent to 7/4 but not numeric; options strictly separated from it
noncomputable abbrev XW : IGame := !{{W, TH} | {2}}

set_option maxHeartbeats 3000000 in
theorem qxw : Q + XW - TH ≈ 1 := by game_cmp

theorem sepOf {y : IGame} [Numeric y] :
    (∀ e ∈ y.moves .left, e < y) ∧ (∀ f ∈ (-y).moves .left, f < -y) :=
  ⟨fun _ he => Numeric.left_lt he, fun _ hf => Numeric.left_lt hf⟩

theorem sepW : (∀ e ∈ W.moves .left, e < W) ∧ (∀ f ∈ (-W).moves .left, f < -W) := by
  refine ⟨fun e he => ?_, fun f hf => ?_⟩
  · simp at he; subst he; game_cmp
  · rw [moves_neg, Set.mem_neg] at hf; simp at hf

theorem sepXW : (∀ e ∈ XW.moves .left, e < XW) ∧ (∀ f ∈ (-XW).moves .left, f < -XW) := by
  refine ⟨fun e he => ?_, fun f hf => ?_⟩
  · simp at he; rcases he with rfl | rfl <;> game_cmp
  · rw [moves_neg, Set.mem_neg] at hf; simp at hf
    have : f = -2 := by rw [← hf, neg_neg]
    subst this; game_cmp

-- helper: IH1 for ½ and XW (only P4 0 1 matters: options strictly separated)
theorem ih1HXW : (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».IH1) ½ XW := by
  intro p q x₁ x₂ y' h1 h2 hy'
  have key : (∀ e ∈ y'.moves .left, e < y') ∧ (∀ f ∈ (-y').moves .left, f < -y') := by
    rcases hy' with rfl | ⟨u, hu⟩
    · exact sepXW
    · cases u <;> simp at hu
      · rcases hu with rfl | rfl
        · exact sepW
        · exact sepOf
      · subst hu; exact sepOf
  have e1 : x₁ = 0 ∨ x₁ = 1 := by cases p <;> simp at h1 <;> simp [h1]
  have e2 : x₂ = 0 ∨ x₂ = 1 := by cases q <;> simp at h2 <;> simp [h2]
  rcases e1 with rfl | rfl <;> rcases e2 with rfl | rfl
  · exact ⟨fun _ => rfl, fun h => absurd h (lt_irrefl _)⟩
  · refine ⟨fun e => absurd e (by game_cmp), fun _ => ⟨fun e he => ?_, fun f hf => ?_⟩⟩
    · change Game.mk (0 * y') + Game.mk (1 * e) < Game.mk (0 * e) + Game.mk (1 * y')
      simp only [zero_mul, one_mul, Game.mk_zero, zero_add]
      exact Game.mk_lt_mk.2 (key.1 e he)
    · change Game.mk (0 * -y') + Game.mk (1 * f) < Game.mk (0 * f) + Game.mk (1 * -y')
      simp only [zero_mul, one_mul, Game.mk_zero, zero_add]
      exact Game.mk_lt_mk.2 (key.2 f hf)
  · exact ⟨fun e => absurd e (by game_cmp), fun l => absurd l (by game_cmp)⟩
  · exact ⟨fun _ => rfl, fun h => absurd h (lt_irrefl _)⟩

-- helper: the same failure with x = XW
theorem key3 : ¬ Game.mk (mulOption XW ½ W 0) < -Game.mk (mulOption XW (-½) TH (-1)) := by
  rw [Game.mk_mulOption, Game.mk_mulOption]
  simp only [mul_zero, mul_neg, mul_one, Game.mk_zero, Game.mk_neg, add_zero, sub_zero]
  rw [Game.mk_eq wHalf, Game.mk_eq thHalf]
  have e := Game.mk_eq qxw
  simp only [Game.mk_sub, Game.mk_add, Game.mk_one] at e
  intro hlt
  have : (1 : Game) < 1 := by
    calc (1 : Game) < -(-Game.mk Q + -Game.mk XW - -Game.mk TH) := hlt
      _ = Game.mk Q + Game.mk XW - Game.mk TH := by abel
      _ = 1 := e
  exact lt_irrefl _ this




-- helpers for IH3_of_IH idx 6: X0 = {0 | 0, 1} ≈ star, X2 = {star | 0, 1}, W = {up |} ≈ 1;
-- X0 * up is not equivalent to star * up, all products are computed one by one
noncomputable abbrev X0 : IGame := !{{0} | {0, 1}}
noncomputable abbrev X2 : IGame := !{{⋆} | {0, 1}}
noncomputable abbrev N2 : IGame := !{{0, ⋆} | {0, ⋆}}
noncomputable abbrev H2 : IGame := !{{N2, 0, ⋆} | {⋆, 0}}

set_option maxHeartbeats 3000000 in
theorem c1 : ¬ X0 * IGame.up ≈ ⋆ * IGame.up := by game_cmp
set_option maxHeartbeats 3000000 in
theorem d3 : X0 * W ≈ 0 := by game_cmp
set_option maxHeartbeats 3000000 in
theorem c3 : X0 * W + IGame.up < X0 * IGame.up + W := by game_cmp
set_option maxHeartbeats 3000000 in
theorem d2 : ⋆ * IGame.up ≈ N2 := by game_cmp
set_option maxHeartbeats 3000000 in
theorem d4 : ⋆ * W ≈ 0 := by game_cmp
set_option maxHeartbeats 3000000 in
theorem d5 : X2 * IGame.up ≈ H2 := by game_cmp
noncomputable abbrev A : IGame := !{{0} | {!{{N2, 0, ⋆} | {N2, 0, ⋆}}, N2}}
noncomputable abbrev K' : IGame := !{{A} | {H2, W + H2 - IGame.up}}

set_option maxHeartbeats 3000000 in
theorem hA : H2 - N2 ≈ A := by game_cmp

theorem m1 : mulOption X2 W ⋆ IGame.up ≈ A := by
  rw [← Game.mk_eq_mk, Game.mk_mulOption, Game.mk_eq d4, Game.mk_eq d5, Game.mk_eq d2, ← Game.mk_eq hA]
  simp

theorem m2 : mulOption X2 W 0 IGame.up ≈ H2 := by
  rw [← Game.mk_eq_mk, Game.mk_mulOption, Game.mk_eq d5]
  simp

theorem m3 : mulOption X2 W 1 IGame.up ≈ W + H2 - IGame.up := by
  rw [← Game.mk_eq_mk, Game.mk_mulOption, Game.mk_eq d5]
  simp

theorem d6 : X2 * W ≈ K' := by
  apply equiv_of_exists
  · intro a ha
    rw [moves_mul] at ha
    obtain ⟨⟨c, d⟩, hcd, rfl⟩ := ha
    simp at hcd
    obtain ⟨rfl, rfl⟩ := hcd
    exact ⟨A, by simp, m1⟩
  · intro a ha
    rw [moves_mul] at ha
    obtain ⟨⟨c, d⟩, hcd, rfl⟩ := ha
    simp at hcd
    obtain ⟨hc, rfl⟩ := hcd
    rcases hc with rfl | rfl
    · exact ⟨H2, by simp, m2⟩
    · exact ⟨W + H2 - IGame.up, by simp, m3⟩
  · intro b hb
    simp at hb
    subst hb
    exact ⟨_, mulOption_mem_moves_mul (px := .left) (py := .left) (by simp) (by simp), m1⟩
  · intro b hb
    simp at hb
    rcases hb with rfl | rfl
    · exact ⟨_, mulOption_mem_moves_mul (px := .right) (py := .left) (by simp) (by simp), m2⟩
    · exact ⟨_, mulOption_mem_moves_mul (px := .right) (py := .left) (by simp) (by simp), m3⟩

theorem f1 : 0 ≤ A := by game_cmp
theorem f2 : A ⧏ H2 := by game_cmp
set_option maxHeartbeats 3000000 in
theorem f3 : A ⧏ W + H2 - IGame.up := by game_cmp

theorem e4 : A < K' := by
  refine lt_of_le_not_ge ?_ (left_lf (by simp))
  rw [le_iff_forall_lf]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · simp at ha; subst ha
    exact lf_of_le_left f1 (by simp)
  · simp at hb
    rcases hb with rfl | rfl
    · exact f2
    · exact f3

theorem c2 : X0 * W ≈ ⋆ * W := d3.trans d4.symm

theorem hl6 : mulOption X2 W ⋆ IGame.up < X2 * W := by
  rw [← Game.mk_lt_mk, Game.mk_eq m1, Game.mk_eq d6, Game.mk_lt_mk]; exact e4

theorem ih24X : (priv% _private.CombinatorialGames.Surreal.Multiplication.«0».IH24) X0 X2 W := by
  intro p z
  refine ⟨fun hz => ?_, fun hz => ?_, fun hz => ?_⟩
  · have : z = 0 ∨ z = 1 := by cases p <;> simp at hz <;> simp [hz]
    rcases this with rfl | rfl
    · exact ⟨fun e => absurd e (by game_cmp), fun l => absurd l (by game_cmp)⟩
    · exact ⟨fun e => absurd e (by game_cmp), fun l => absurd l (by game_cmp)⟩
  · have : z = ⋆ ∨ z = 0 ∨ z = 1 := by cases p <;> simp at hz <;> simp [hz]
    rcases this with rfl | rfl | rfl
    · exact ⟨fun _ => Game.mk_eq c2, fun l => absurd l (by game_cmp)⟩
    · exact ⟨fun e => absurd e (by game_cmp), fun l => absurd l (by game_cmp)⟩
    · refine ⟨fun e => absurd e (by game_cmp), fun _ => ⟨fun a ha => ?_, fun b hb => ?_⟩⟩
      · simp at ha; subst ha
        change Game.mk (X0 * W) + Game.mk (1 * IGame.up) < Game.mk (X0 * IGame.up) + Game.mk (1 * W)
        rw [one_mul, one_mul, ← Game.mk_add, ← Game.mk_add, Game.mk_lt_mk]; exact c3
      · rw [moves_neg] at hb; simp at hb
  · obtain rfl : z = IGame.up := by cases p <;> simpa using hz
    exact ⟨fun e => absurd e (by game_cmp), fun l => absurd l (by game_cmp)⟩

end T2c0

open IGame Set T2c0

-- `_private.CombinatorialGames.Surreal.Multiplication.0.mulOption_lt_of_lt` idx 10
theorem t2_10 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».mulOption_lt_of_lt 10 :=
  fun h => key10 (@h SF ½ _ ih1Num ih1Num W 0 TH (-1) (by game_cmp) (by simp) (by simp) (by simp))

-- `_private.CombinatorialGames.Surreal.Multiplication.0.mulOption_lt_of_lt` idx 3
theorem t2_3 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».mulOption_lt_of_lt 3 :=
  fun h => key3 (@h XW ½ _ ih1HXW W 0 TH (-1) (by game_cmp) (by simp) (by simp) (by simp) (by simp))

-- `_private.CombinatorialGames.Surreal.Multiplication.0.IH3_of_IH` idx 6
theorem t2_6 : ¬ drop0% _private.CombinatorialGames.Surreal.Multiplication.«0».IH3_of_IH 6 := fun h => by
  have := (@h X0 X2 W ⋆ IGame.up ih24X (by simp) (by simp) hl6).1 (by game_cmp)
  exact c1 (Game.mk_eq_mk.1 this)
