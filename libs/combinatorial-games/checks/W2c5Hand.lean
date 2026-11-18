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

namespace W2c5
open IGame

def Cm (z : IGame) : Prop := ∃ c, c ∈ z.moves .left ∧ c ∈ z.moves .right

theorem notNum {z : IGame} (h : Cm z) : ¬ Numeric z := fun hn => by
  obtain ⟨c, h1, h2⟩ := h
  exact lt_irrefl c (Numeric.left_lt_right h1 h2)

theorem cmNeg {z : IGame} (h : Cm z) : Cm (-z) := by
  obtain ⟨c, h1, h2⟩ := h
  exact ⟨-c, by simpa [moves_neg] using h2, by simpa [moves_neg] using h1⟩

theorem cmAddL (w : IGame) {z : IGame} (h : Cm z) : Cm (w + z) := by
  obtain ⟨c, h1, h2⟩ := h
  exact ⟨_, add_left_mem_moves_add h1 w, add_left_mem_moves_add h2 w⟩

theorem cmAddR (w : IGame) {z : IGame} (h : Cm z) : Cm (z + w) := by
  obtain ⟨c, h1, h2⟩ := h
  exact ⟨_, add_right_mem_moves_add h1 w, add_right_mem_moves_add h2 w⟩

theorem cmSubR (w : IGame) {z : IGame} (h : Cm z) : Cm (w - z) := by
  rw [sub_eq_add_neg]; exact cmAddL w (cmNeg h)

theorem cmMulL {w z : IGame} {p : Player} {a : IGame} (ha : a ∈ w.moves p) (h : Cm z) : Cm (w * z) := by
  obtain ⟨c, h1, h2⟩ := h
  cases p
  · exact ⟨_, mulOption_mem_moves_mul (px := .left) (py := .left) ha h1,
      mulOption_mem_moves_mul (px := .left) (py := .right) ha h2⟩
  · exact ⟨_, mulOption_mem_moves_mul (px := .right) (py := .right) ha h2,
      mulOption_mem_moves_mul (px := .right) (py := .left) ha h1⟩

theorem cmMulR {w z : IGame} {p : Player} {a : IGame} (ha : a ∈ w.moves p) (h : Cm z) : Cm (z * w) := by
  rw [mul_comm]; exact cmMulL ha h

theorem cmStar : Cm IGame.star := ⟨0, by simp [IGame.star], by simp [IGame.star]⟩

-- if 0 < x and x has no positive option, x⁻¹ = 1
theorem invMoves_triv {x : IGame} (hx : 0 < x) (hno : ∀ p, ∀ y ∈ x.moves p, ¬ 0 < y) :
    ∀ p y, y ∈ x⁻¹.moves p → p = .left ∧ y = 0 :=
  invRec hx (P := fun p y _ => p = .left ∧ y = 0) ⟨rfl, rfl⟩
    (fun _ _ y hy hyx _ _ _ => absurd hy (hno _ y hyx))

theorem inv_eq_one {x : IGame} (hx : 0 < x) (hno : ∀ p, ∀ y ∈ x.moves p, ¬ 0 < y) : x⁻¹ = 1 := by
  ext p y
  cases p
  · constructor
    · intro h; have := (invMoves_triv hx hno _ _ h).2; simp [this]
    · intro h; simp at h; subst h; exact zero_mem_moves_left_inv hx
  · constructor
    · intro h; exact absurd (invMoves_triv hx hno _ _ h).1 (by decide)
    · intro h; simp at h

theorem oneInv : (1 : IGame)⁻¹ = 1 :=
  inv_eq_one (by game_cmp) (fun p y hy => by cases p <;> simp at hy; subst hy; exact lt_irrefl 0)

theorem upInv : IGame.up⁻¹ = 1 :=
  inv_eq_one (by game_cmp) (fun p y hy => by
    cases p <;> simp [IGame.up] at hy <;> subst hy
    · exact lt_irrefl 0
    · game_cmp)

open Classical in
theorem starInv : IGame.star⁻¹ = 0 := by
  show (if 0 < IGame.star then _ else if IGame.star < 0 then _ else 0) = 0
  rw [ite_cond_eq_false _ _ (eq_false (by game_cmp)), ite_cond_eq_false _ _ (eq_false (by game_cmp))]

noncomputable def X : IGame := !{{1} | {1}}
theorem X_pos : 0 < X := by unfold X; game_cmp
theorem cmX : Cm X := ⟨1, by simp [X], by simp [X]⟩
theorem io10 : invOption X 1 0 = 1 := by simp [invOption, IGame.div_eq_mul_inv, oneInv]
theorem one_R_Xinv : (1 : IGame) ∈ X⁻¹.moves .right := by
  have := invOption_mem_moves_inv (p₁ := .left) (p₂ := .right) X_pos (y := 1) (by game_cmp)
    (by simp [X]) (zero_mem_moves_left_inv X_pos)
  rwa [io10] at this
theorem one_L_Xinv : (1 : IGame) ∈ X⁻¹.moves .left := by
  have := invOption_mem_moves_inv (p₁ := .left) (p₂ := .left) X_pos (y := 1) (by game_cmp)
    (by simp [X]) (zero_mem_moves_left_inv X_pos)
  rwa [io10] at this
theorem cmXinv : Cm X⁻¹ := ⟨1, one_L_Xinv, one_R_Xinv⟩
theorem notNumXinv : ¬ Numeric X⁻¹ := notNum cmXinv
-- a non-numeric right option of X⁻¹
theorem badR : (1 + (1 - X)) ∈ X⁻¹.moves .right := by
  have := invOption_mem_moves_inv (p₁ := .right) (p₂ := .right) X_pos (y := 1) (by game_cmp)
    (by simp [X]) one_R_Xinv
  simpa [invOption, IGame.div_eq_mul_inv, oneInv] using this
theorem notNumBad : ¬ Numeric (1 + (1 - X)) := notNum (cmAddL 1 (cmSubR 1 cmX))
theorem hlX : ∀ y ∈ X.moves .left, 0 < y → Numeric y⁻¹ := by
  intro y hy _; simp [X] at hy; subst hy; infer_instance
theorem hrX : ∀ y ∈ X.moves .right, Numeric y⁻¹ := by
  intro y hy; simp [X] at hy; subst hy; infer_instance
theorem hlX' : ∀ y ∈ X.moves .left, 0 < y → y * y⁻¹ ≈ 1 := by
  intro y hy _; simp [X] at hy; subst hy; rw [oneInv, mul_one]
theorem hrX' : ∀ y ∈ X.moves .right, y * y⁻¹ ≈ 1 := by
  intro y hy; simp [X] at hy; subst hy; rw [oneInv, mul_one]


noncomputable def gapX : IGame := !{Set.range (Nat.cast : ℕ → IGame) | Set.range (Nat.cast : ℕ → IGame)}
theorem gapX_le_iff (Y : IGame) [IGame.Numeric Y] : gapX ≤ Y ↔ ∀ n : ℕ, (n : IGame) < Y := by
  constructor
  · intro h n
    have := (IGame.le_iff_forall_lf.1 h).1 (n : IGame) (by simp [gapX])
    exact IGame.Numeric.not_le.1 this
  · intro h
    rw [IGame.le_iff_forall_lf]
    refine ⟨fun z hz => ?_, fun z hz => ?_⟩
    · simp only [gapX, IGame.moves_left_ofSets, Set.mem_range] at hz
      obtain ⟨n, rfl⟩ := hz
      exact (h n).not_ge
    · refine IGame.lf_of_right_le (z := (0 : ℕ)) ?_ (by simp [gapX])
      have := (h 0).trans (IGame.Numeric.lt_right hz)
      exact this.le
theorem gapX_le_iff' (y : Surreal) : Game.mk gapX ≤ y.toGame ↔ ∀ n : ℕ, (n : Surreal) < y := by
  cases y with | mk Y
  rw [Surreal.toGame_mk, Game.mk_le_mk, gapX_le_iff]
  simp only [← Surreal.mk_natCast, Surreal.mk_lt_mk]
theorem notNumericGap : ¬ (Surreal.Cut.leftGame (Game.mk gapX)).Numeric := fun hN => by
  obtain ⟨z, hz⟩ | ⟨z, hz⟩ := Surreal.Cut.numeric_def.1 hN
  · have H : ∀ y, z ≤ y ↔ ∀ n : ℕ, (n : Surreal) < y := fun y => by
      rw [← gapX_le_iff', ← Surreal.Cut.mem_right_leftGame, ← hz, Surreal.Cut.right_leftSurreal, Set.mem_Ici]
    have h1 := (H z).1 le_rfl
    have h2 : z ≤ z - 1 := (H (z - 1)).2 fun n => by
      have := h1 (n + 1); push_cast at this; linarith
    linarith
  · have H : ∀ y, y ≤ z ↔ ¬ (Game.mk gapX ≤ y.toGame) := fun y => by
      rw [← Set.mem_Iic, ← Surreal.Cut.left_rightSurreal, hz, Surreal.Cut.mem_left_leftGame]
    have h1 := (H z).1 le_rfl
    rw [gapX_le_iff'] at h1
    push Not at h1
    obtain ⟨n, hn⟩ := h1
    have h2 : z + 1 ≤ z := (H (z + 1)).2 fun h => by
      rw [gapX_le_iff'] at h
      have := h (n + 1); push_cast at this; linarith
    linarith

noncomputable def natG : IGame.{0} := !{Set.range (fun n : ℕ => (n : IGame.{0})) | ∅}
noncomputable def natR : IGame.{0} := !{∅ | Set.range (fun n : ℕ => -(n : IGame.{0}))}

theorem gap_le : Surreal.Cut.infRight gapX ≤ Surreal.Cut.supLeft gapX := by
  have h0 : ((0 : ℕ) : IGame) ∈ gapX.moves .left := by simp [gapX]
  have h0' : ((0 : ℕ) : IGame) ∈ gapX.moves .right := by simp [gapX]
  have h1 : Surreal.Cut.infRight gapX ≤ Surreal.Cut.leftGame (Game.mk ((0 : ℕ) : IGame)) :=
    iInf₂_le (f := fun i (_ : i ∈ gapX.moves .right) => Surreal.Cut.leftGame (Game.mk i)) _ h0'
  have h2 : Surreal.Cut.rightGame (Game.mk ((0 : ℕ) : IGame)) ≤ Surreal.Cut.supLeft gapX :=
    le_iSup₂ (f := fun i (_ : i ∈ gapX.moves .left) => Surreal.Cut.rightGame (Game.mk i)) _ h0
  rw [Surreal.Cut.leftGame_mk_of_numeric] at h1
  rw [Surreal.Cut.rightGame_mk_of_numeric] at h2
  exact h1.trans ((Surreal.Cut.leftSurreal_lt_rightSurreal _).le.trans h2)

end W2c5

open IGame W2c5

-- `Surreal.Cut.leftGame_switch_of_numeric`
theorem c5_17 : ¬ drop0% Surreal.Cut.leftGame_switch_of_numeric 1 := fun h => by
  have e := @h (-1) _
  rw [Game.mk_eq (show (±(-1 : IGame)) ≈ 0 by game_cmp), Surreal.Cut.leftGame_mk_of_numeric] at e
  exact Surreal.Cut.leftSurreal_ne_rightSurreal _ _ e
-- `Surreal.Cut.rightGame_switch_of_numeric`
theorem c5_18 : ¬ drop0% Surreal.Cut.rightGame_switch_of_numeric 1 := fun h => by
  have e := @h (-1) _
  rw [Game.mk_eq (show (±(-1 : IGame)) ≈ 0 by game_cmp), Surreal.Cut.rightGame_mk_of_numeric,
    Surreal.Cut.neg_rightSurreal] at e
  exact Surreal.Cut.rightSurreal_ne_leftSurreal _ _ e
-- `Surreal.Cut.rightGame_switch_of_numeric`
theorem c5_19 : ¬ indep0% Surreal.Cut.rightGame_switch_of_numeric 2 := fun h =>
  not_numeric_star (Numeric.of_mem_moves (p := .right) (x := IGame.up) (by simp [IGame.up]) (h := @h IGame.up (by game_cmp)))
-- `Surreal.Cut.supLeft_mem_of_short`
theorem c5_20 : ¬ drop0% Surreal.Cut.supLeft_mem_of_short 1 := fun h => by
  obtain ⟨y, hy, e⟩ := @h natG ⟨((0 : ℕ) : IGame), by simp [natG]⟩
  simp only [natG, moves_left_ofSets, Set.mem_range] at hy
  obtain ⟨n, rfl⟩ := hy
  have h1 : Surreal.Cut.rightGame (Game.mk ((n + 1 : ℕ) : IGame)) ≤ Surreal.Cut.supLeft natG :=
    le_iSup₂ (f := fun i (_ : i ∈ natG.moves .left) => Surreal.Cut.rightGame (Game.mk i)) _ (by simp only [natG, moves_left_ofSets]; exact ⟨n + 1, rfl⟩)
  rw [← e, Surreal.Cut.rightGame_mk_of_numeric, Surreal.Cut.rightGame_mk_of_numeric] at h1
  simp at h1; exact absurd h1 (by norm_num)
-- `Surreal.Cut.infRight_mem_of_short`
theorem c5_21 : ¬ drop0% Surreal.Cut.infRight_mem_of_short 1 := fun h => by
  obtain ⟨y, hy, e⟩ := @h natR ⟨-((0 : ℕ) : IGame), by simp [natR]⟩
  simp only [natR, moves_right_ofSets, Set.mem_range] at hy
  obtain ⟨n, rfl⟩ := hy
  have h1 : Surreal.Cut.infRight natR ≤ Surreal.Cut.leftGame (Game.mk (-((n + 1 : ℕ) : IGame))) :=
    iInf₂_le (f := fun i (_ : i ∈ natR.moves .right) => Surreal.Cut.leftGame (Game.mk i)) _ (by simp only [natR, moves_right_ofSets]; exact ⟨n + 1, rfl⟩)
  rw [← e, Surreal.Cut.leftGame_mk_of_numeric, Surreal.Cut.leftGame_mk_of_numeric] at h1
  simp at h1; exact absurd h1 (by norm_num)
-- `_private.CombinatorialGames.Surreal.Cut.0.Surreal.Cut.Numeric.short_aux`
theorem c5_22 : ¬ drop0% _private.CombinatorialGames.Surreal.Cut.«0».Surreal.Cut.Numeric.short_aux 1 := fun h =>
  notNumericGap (h gapX).1
-- `Surreal.Cut.Numeric.leftGame`
theorem c5_23 : ¬ drop0% Surreal.Cut.Numeric.leftGame 1 := fun h => notNumericGap (h gapX)
-- `Surreal.Cut.Numeric.rightGame`
theorem c5_24 : ¬ drop0% Surreal.Cut.Numeric.rightGame 1 := fun h => by
  have := h (-gapX)
  rw [Game.mk_neg, Surreal.Cut.rightGame_neg] at this
  exact notNumericGap (by simpa using (inferInstance : (-(-Surreal.Cut.leftGame (Game.mk gapX))).Numeric))
-- `Surreal.Cut.Numeric.supLeft`
theorem c5_25 : ¬ drop0% Surreal.Cut.Numeric.supLeft 1 := fun h => by
  have := @h gapX ⟨((0 : ℕ) : IGame), by simp only [gapX, moves_left_ofSets]; exact ⟨0, rfl⟩⟩
  rw [← Surreal.Cut.leftGame_eq_supLeft_of_le gap_le] at this
  exact notNumericGap this
-- `Surreal.Cut.Numeric.supLeft`
theorem c5_26 : ¬ drop0% Surreal.Cut.Numeric.supLeft 2 := fun h => by
  have := @h 0 _
  rw [show Surreal.Cut.supLeft 0 = ⊥ by simp [Surreal.Cut.supLeft]] at this
  exact Surreal.Cut.Numeric.ne_bot _ rfl
-- `Surreal.Cut.Numeric.infRight`
theorem c5_27 : ¬ drop0% Surreal.Cut.Numeric.infRight 2 := fun h => by
  have := @h 0 _
  rw [show Surreal.Cut.infRight 0 = ⊤ by simp [Surreal.Cut.infRight]] at this
  exact Surreal.Cut.Numeric.ne_top _ rfl
-- `Surreal.Cut.Numeric.infRight`
theorem c5_28 : ¬ drop0% Surreal.Cut.Numeric.infRight 1 := fun h => by
  have := @h (-gapX) ⟨-((0 : ℕ) : IGame), by
    first | (simp [gapX]; done) | (simp [gapX]; exact ⟨0, by simp⟩)⟩
  rw [Surreal.Cut.infRight_neg, ← Surreal.Cut.leftGame_eq_supLeft_of_le gap_le] at this
  exact notNumericGap (by simpa using (inferInstance : (-(-Surreal.Cut.leftGame (Game.mk gapX))).Numeric))

namespace W2c5
open IGame

theorem mkTwo (x : IGame) : Game.mk (x * 2) = Game.mk (x + x) := by
  rw [← one_add_one_eq_two, Game.mk_eq_mk.2 (mul_add_equiv x 1 1)]
  simp

theorem twoInv : (2 : IGame)⁻¹ ≈ IGame.half := by
  rw [← Surreal.mk_eq_mk, IGame.mk_half]; simp; exact_mod_cast Surreal.mk_natCast 2

noncomputable def Z : IGame := !{{0, IGame.star} | {IGame.star}}
theorem Z_pos : 0 < Z := by unfold Z; game_cmp
theorem cmZ : Cm Z := ⟨IGame.star, by simp [Z], by simp [Z]⟩
theorem ZInv : Z⁻¹ = 1 :=
  inv_eq_one Z_pos (fun p y hy => by
    cases p <;> simp [Z] at hy
    · rcases hy with rfl | rfl
      · exact lt_irrefl 0
      · game_cmp
    · subst hy; game_cmp)

noncomputable def N : IGame := !{∅ | {-1}}
instance N_num : Numeric N :=
  numeric_def.2 ⟨by simp [N], fun p y hy => by cases p <;> simp [N] at hy; subst hy; infer_instance⟩
theorem N_neg : 0 < -N := by unfold N; game_cmp

-- for numeric positive x, the conclusion of the private lemma mul_inv_option_mem
theorem mio (x : IGame) [Numeric x] (hx : 0 < x) :
    (∀ y ∈ x⁻¹.moves .left, x * y < 1) ∧ (∀ y ∈ x⁻¹.moves .right, 1 < x * y) := by
  have h1 := Numeric.mul_inv_cancel (x := x) hx.not_antisymmRel_symm
  constructor
  · intro y hy
    have := Numeric.of_mem_moves hy
    exact lt_of_lt_of_le ((Numeric.mul_lt_mul_iff_right hx).2 (Numeric.left_lt hy)) h1.le
  · intro y hy
    have := Numeric.of_mem_moves hy
    exact lt_of_le_of_lt h1.symm.le ((Numeric.mul_lt_mul_iff_right hx).2 (Numeric.lt_right hy))

-- for numeric x, the conclusion of the private lemma option_mul_inv_lt
theorem omil (x : IGame) [Numeric x] :
    (∀ y ∈ (x * x⁻¹).moves .left, y < 1) ∧ (∀ y ∈ (x * x⁻¹).moves .right, 1 < y) := by
  by_cases h0 : x ≈ 0
  · rw [inv_of_equiv_zero h0, mul_zero]; simp
  have h1 := Numeric.mul_inv_cancel h0
  constructor
  · intro y hy
    have := Numeric.of_mem_moves hy
    exact lt_of_lt_of_le (Numeric.left_lt hy) h1.le
  · intro y hy
    have := Numeric.of_mem_moves hy
    exact lt_of_le_of_lt h1.symm.le (Numeric.lt_right hy)

theorem notEqStar (r : IGame) [Numeric r] : ¬ IGame.star ≈ r := fun h => by
  obtain h0 | h0 | h0 := Numeric.lt_or_equiv_or_gt r 0
  · exact absurd (lt_of_le_of_lt h.le h0) (by game_cmp)
  · exact absurd (h.trans h0) (by game_cmp)
  · exact absurd (lt_of_lt_of_le h0 h.symm.le) (by game_cmp)

end W2c5

open IGame W2c5

-- `_private.CombinatorialGames.Surreal.Division.0.instNumericHDivIGameOfInv`
theorem c5_30 : ¬ drop0% _private.CombinatorialGames.Surreal.Division.«0».instNumericHDivIGameOfInv 3 := fun h =>
  notNumXinv (by simpa [IGame.div_eq_mul_inv] using @h 1 X _)
-- `_private.CombinatorialGames.Surreal.Division.0.instNumericInvOptionOfInvIGame`
theorem c5_31 : ¬ drop0% _private.CombinatorialGames.Surreal.Division.«0».instNumericInvOptionOfInvIGame 3 := fun h => by
  have := @h IGame.star 1 1 _ _ _
  rw [invOption, IGame.div_eq_mul_inv, oneInv, mul_one, mul_one] at this
  exact notNum (cmAddL 1 (cmSubR 1 cmStar)) this
-- `_private.CombinatorialGames.Surreal.Division.0.instNumericInvOptionOfInvIGame`
theorem c5_32 : ¬ drop0% _private.CombinatorialGames.Surreal.Division.«0».instNumericInvOptionOfInvIGame 4 := fun h => by
  have := @h 0 Z 1 _ (by rw [ZInv]; infer_instance) _
  rw [invOption, IGame.div_eq_mul_inv, ZInv, mul_one, mul_one, sub_eq_add_neg] at this
  exact notNum (cmAddL 1 (cmAddR _ cmZ)) this
-- `_private.CombinatorialGames.Surreal.Division.0.instNumericInvOptionOfInvIGame`
theorem c5_33 : ¬ drop0% _private.CombinatorialGames.Surreal.Division.«0».instNumericInvOptionOfInvIGame 6 := fun h => by
  have := @h 0 1 IGame.star _ _ _
  simp only [invOption, IGame.div_eq_mul_inv, oneInv, mul_one, sub_zero, one_mul] at this
  exact notNum (cmAddL 1 cmStar) this
-- `_private.CombinatorialGames.Surreal.Division.0.mk_div'`
theorem c5_34 : ¬ indep0% _private.CombinatorialGames.Surreal.Division.«0».mk_div' 2 := fun h =>
  not_numeric_star (by first | exact @h IGame.star 0 | exact @h IGame.star 0 (by rw [IGame.inv_zero]; exact Numeric.zero))
-- `_private.CombinatorialGames.Surreal.Division.0.mk_div'`
theorem c5_35 : ¬ indep0% _private.CombinatorialGames.Surreal.Division.«0».mk_div' 3 := fun h =>
  notNumXinv (by first | exact @h 0 X _ | exact @h 0 X)
-- `_private.CombinatorialGames.Surreal.Division.0.one_neg_mul_invOption`
theorem c5_36 : ¬ drop0% _private.CombinatorialGames.Surreal.Division.«0».one_neg_mul_invOption 2 := fun h => by
  have := @h 1 0 0 _ _ (by rw [IGame.inv_zero]; exact Numeric.zero) _
  simp [invOption, IGame.div_eq_mul_inv] at this
  exact absurd this (by game_cmp)
-- `_private.CombinatorialGames.Surreal.Division.0.mulOption_le`
theorem c5_37 : ¬ drop0% _private.CombinatorialGames.Surreal.Division.«0».mulOption_le 8 := fun h => by
  have := @h 0 0 (-1) 1 _ _ _ (by game_cmp)
  simp [mulOption] at this
  exact absurd this (by game_cmp)
-- `_private.CombinatorialGames.Surreal.Division.0.le_mulOption`
theorem c5_38 : ¬ drop0% _private.CombinatorialGames.Surreal.Division.«0».le_mulOption 8 := fun h => by
  have := @h 0 1 (-1) 0 _ _ _ (by game_cmp)
  simp [mulOption] at this
  exact absurd this (by game_cmp)
-- `_private.CombinatorialGames.Surreal.Division.0.numeric_option_inv`
theorem c5_39 : ¬ drop0% _private.CombinatorialGames.Surreal.Division.«0».numeric_option_inv 1 := fun h =>
  notNumBad (@h X X_pos hlX hrX .right _ badR)
-- `_private.CombinatorialGames.Surreal.Division.0.numeric_option_inv`
theorem c5_40 : drop% _private.CombinatorialGames.Surreal.Division.«0».numeric_option_inv 2 := by
  intro x inst _ _ p y hy; exact Numeric.of_mem_moves hy
-- `_private.CombinatorialGames.Surreal.Division.0.numeric_option_inv`
theorem c5_41 : drop% _private.CombinatorialGames.Surreal.Division.«0».numeric_option_inv 3 := by
  intro x inst _ _ p y hy; exact Numeric.of_mem_moves hy
-- `_private.CombinatorialGames.Surreal.Division.0.mul_inv_option_mem`
theorem c5_42 : ¬ drop0% _private.CombinatorialGames.Surreal.Division.«0».mul_inv_option_mem 1 := fun h => by
  have := (@h X X_pos hlX hrX hlX' hrX').2 1 one_R_Xinv
  rw [mul_one] at this
  exact absurd this (by unfold X; game_cmp)
-- `_private.CombinatorialGames.Surreal.Division.0.mul_inv_option_mem`
theorem c5_43 : ¬ drop0% _private.CombinatorialGames.Surreal.Division.«0».mul_inv_option_mem 2 := fun h => by
  have hr : ∀ y ∈ N.moves .right, Numeric y⁻¹ := by
    intro y hy; simp [N] at hy; subst hy; infer_instance
  have hr' : ∀ y ∈ N.moves .right, y * y⁻¹ ≈ 1 := by
    intro y hy; simp [N] at hy; subst hy; exact Numeric.mul_inv_cancel (by game_cmp)
  have := (@h N _ (by simp [N]) hr (by simp [N]) hr').2 0 (by
    have e : N⁻¹ = -(-N)⁻¹ := by rw [← IGame.inv_neg, neg_neg]
    rw [e, moves_neg]; simpa using zero_mem_moves_left_inv N_neg)
  rw [mul_zero] at this
  exact absurd this (by game_cmp)
-- `_private.CombinatorialGames.Surreal.Division.0.mul_inv_option_mem`
theorem c5_44 : drop% _private.CombinatorialGames.Surreal.Division.«0».mul_inv_option_mem 3 := by
  intro x inst hx; intros; exact mio x hx
-- `_private.CombinatorialGames.Surreal.Division.0.mul_inv_option_mem`
theorem c5_45 : drop% _private.CombinatorialGames.Surreal.Division.«0».mul_inv_option_mem 4 := by
  intro x inst hx; intros; exact mio x hx
-- `_private.CombinatorialGames.Surreal.Division.0.mul_inv_option_mem`
theorem c5_46 : drop% _private.CombinatorialGames.Surreal.Division.«0».mul_inv_option_mem 5 := by
  intro x inst hx; intros; exact mio x hx
-- `_private.CombinatorialGames.Surreal.Division.0.mul_inv_option_mem`
theorem c5_47 : drop% _private.CombinatorialGames.Surreal.Division.«0».mul_inv_option_mem 6 := by
  intro x inst hx; intros; exact mio x hx
-- `_private.CombinatorialGames.Surreal.Division.0.numeric_inv`
theorem c5_48 : ¬ drop0% _private.CombinatorialGames.Surreal.Division.«0».numeric_inv 1 := fun h =>
  notNumXinv (@h X X_pos hlX hrX hlX' hrX')
-- `_private.CombinatorialGames.Surreal.Division.0.option_mul_inv_lt`
theorem c5_49 : ¬ drop0% _private.CombinatorialGames.Surreal.Division.«0».option_mul_inv_lt 1 := fun h => by
  have hm : mulOption X X⁻¹ 1 0 ∈ (X * X⁻¹).moves .left :=
    mulOption_mem_moves_mul (px := .left) (py := .left) (by simp [X]) (zero_mem_moves_left_inv X_pos)
  have := (@h X X_pos hlX hrX hlX' hrX').1 _ hm
  rw [mulOption_zero_right, one_mul] at this
  exact left_lf one_L_Xinv this.le
-- `_private.CombinatorialGames.Surreal.Division.0.option_mul_inv_lt`
theorem c5_50 : drop% _private.CombinatorialGames.Surreal.Division.«0».option_mul_inv_lt 2 := by
  intro x inst; intros; exact omil x
-- `_private.CombinatorialGames.Surreal.Division.0.option_mul_inv_lt`
theorem c5_51 : drop% _private.CombinatorialGames.Surreal.Division.«0».option_mul_inv_lt 3 := by
  intro x inst; intros; exact omil x
-- `_private.CombinatorialGames.Surreal.Division.0.option_mul_inv_lt`
theorem c5_52 : drop% _private.CombinatorialGames.Surreal.Division.«0».option_mul_inv_lt 4 := by
  intro x inst; intros; exact omil x
-- `_private.CombinatorialGames.Surreal.Division.0.option_mul_inv_lt`
theorem c5_53 : drop% _private.CombinatorialGames.Surreal.Division.«0».option_mul_inv_lt 5 := by
  intro x inst; intros; exact omil x
-- `_private.CombinatorialGames.Surreal.Division.0.option_mul_inv_lt`
theorem c5_54 : drop% _private.CombinatorialGames.Surreal.Division.«0».option_mul_inv_lt 6 := by
  intro x inst; intros; exact omil x
-- `_private.CombinatorialGames.Surreal.Division.0.mul_inv_self`
theorem c5_55 : drop% _private.CombinatorialGames.Surreal.Division.«0».mul_inv_self 3 := by
  intro x inst hx; intros; exact Numeric.mul_inv_cancel hx.not_antisymmRel_symm
-- `_private.CombinatorialGames.Surreal.Division.0.mul_inv_self`
theorem c5_56 : drop% _private.CombinatorialGames.Surreal.Division.«0».mul_inv_self 4 := by
  intro x inst hx; intros; exact Numeric.mul_inv_cancel hx.not_antisymmRel_symm
-- `_private.CombinatorialGames.Surreal.Division.0.mul_inv_self`
theorem c5_57 : drop% _private.CombinatorialGames.Surreal.Division.«0».mul_inv_self 5 := by
  intro x inst hx; intros; exact Numeric.mul_inv_cancel hx.not_antisymmRel_symm
-- `_private.CombinatorialGames.Surreal.Division.0.mul_inv_self`
theorem c5_58 : drop% _private.CombinatorialGames.Surreal.Division.«0».mul_inv_self 6 := by
  intro x inst hx; intros; exact Numeric.mul_inv_cancel hx.not_antisymmRel_symm
-- `_private.CombinatorialGames.Surreal.Division.0.main`
theorem c5_59 : ¬ drop0% _private.CombinatorialGames.Surreal.Division.«0».main 1 := fun h =>
  notNumXinv (@h X X_pos).1

namespace W2c5
open IGame
theorem zz : (1 : IGame) < (IGame.half + (IGame.up + IGame.star)) * 2 := by
  rw [← Game.mk_lt_mk, mkTwo]
  have e : Game.mk ((IGame.half + (IGame.up + IGame.star)) + (IGame.half + (IGame.up + IGame.star))) =
      Game.mk (IGame.half + IGame.half) + Game.mk (IGame.up + IGame.up + (IGame.star + IGame.star)) := by
    simp only [Game.mk_add]; abel
  have h0 : (0 : Game) < Game.mk (IGame.up + IGame.up + (IGame.star + IGame.star)) := by
    rw [← Game.mk_zero, Game.mk_lt_mk]; game_cmp
  rw [e, Game.mk_eq_mk.2 half_add_half_equiv_one]
  exact lt_add_of_pos_right _ h0
theorem nz : ¬ IGame.half < IGame.half + (IGame.up + IGame.star) := by
  rw [← Game.mk_lt_mk, Game.mk_add, lt_add_iff_pos_right, ← Game.mk_zero, Game.mk_lt_mk]; game_cmp
end W2c5

-- `IGame.Numeric.inv`
theorem c5_60 : ¬ drop0% IGame.Numeric.inv 1 := fun h => notNumXinv (h X)
-- `IGame.Numeric.div`
theorem c5_61 : ¬ drop0% IGame.Numeric.div 2 := fun h => by
  have := @h IGame.star 1 _
  rw [IGame.div_eq_mul_inv, oneInv, mul_one] at this
  exact not_numeric_star this
-- `IGame.Numeric.div`
theorem c5_62 : ¬ drop0% IGame.Numeric.div 3 := fun h => by
  have := @h 1 X _
  rw [IGame.div_eq_mul_inv, one_mul] at this
  exact notNumXinv this
-- `IGame.Numeric.invOption`
theorem c5_63 : ¬ drop0% IGame.Numeric.invOption 3 := fun h => by
  have := @h IGame.star 1 1 _ _
  rw [invOption, IGame.div_eq_mul_inv, oneInv, mul_one, mul_one] at this
  exact notNum (cmAddL 1 (cmSubR 1 cmStar)) this
-- `IGame.Numeric.invOption`
theorem c5_64 : ¬ drop0% IGame.Numeric.invOption 4 := fun h => by
  have := @h 0 X 0 _ _
  rw [invOption, IGame.div_eq_mul_inv, mul_zero, add_zero, one_mul] at this
  exact notNumXinv this
-- `IGame.Numeric.invOption`
theorem c5_65 : ¬ drop0% IGame.Numeric.invOption 5 := fun h => by
  have := @h 0 1 IGame.star _ _
  simp only [invOption, IGame.div_eq_mul_inv, oneInv, mul_one, sub_zero, one_mul] at this
  exact notNum (cmAddL 1 cmStar) this
-- `IGame.Numeric.mul_inv_cancel`
theorem c5_66 : ¬ drop0% IGame.Numeric.mul_inv_cancel 1 := fun h => by
  have := @h IGame.star (by game_cmp)
  rw [starInv, mul_zero] at this
  exact absurd this (by game_cmp)
-- `IGame.Numeric.inv_mul_cancel`
theorem c5_67 : ¬ drop0% IGame.Numeric.inv_mul_cancel 1 := fun h => by
  have := @h IGame.star (by game_cmp)
  rw [starInv, zero_mul] at this
  exact absurd this (by game_cmp)
-- `IGame.Numeric.inv_congr`
theorem c5_68 : ¬ drop0% IGame.Numeric.inv_congr 4 := fun h => by
  have := @h 1 0 _ _
  rw [oneInv, IGame.inv_zero] at this
  exact absurd this (by game_cmp)
-- `IGame.Numeric.div_congr_left`
theorem c5_69 : ¬ drop0% IGame.Numeric.div_congr_left 6 := fun h => by
  have := @h 0 1 1 _ _ _
  rw [IGame.div_eq_mul_inv, IGame.div_eq_mul_inv, oneInv, mul_one, mul_one] at this
  exact absurd this (by game_cmp)
-- `IGame.Numeric.div_congr_right`
theorem c5_70 : ¬ drop0% IGame.Numeric.div_congr_right 6 := fun h => by
  have := @h 1 1 0 _ _ _
  rw [IGame.div_eq_mul_inv, IGame.div_eq_mul_inv, oneInv, IGame.inv_zero, mul_one, mul_zero] at this
  exact absurd this (by game_cmp)
-- `IGame.Numeric.div_congr`
theorem c5_71 : ¬ drop0% IGame.Numeric.div_congr 8 := fun h => by
  have := @h 0 1 1 1 _ _ _ _ .rfl
  rw [IGame.div_eq_mul_inv, IGame.div_eq_mul_inv, oneInv, mul_one, mul_one] at this
  exact absurd this (by game_cmp)
-- `IGame.Numeric.div_congr`
theorem c5_72 : ¬ drop0% IGame.Numeric.div_congr 9 := fun h => by
  have := @h 1 1 1 0 _ _ _ _ .rfl
  rw [IGame.div_eq_mul_inv, IGame.div_eq_mul_inv, oneInv, IGame.inv_zero, mul_one, mul_zero] at this
  exact absurd this (by game_cmp)
-- `Surreal.mk_div`
theorem c5_73 : ¬ indep0% Surreal.mk_div 2 := fun h =>
  not_numeric_star (by first | exact @h IGame.star 0 | exact @h IGame.star 0 Numeric.zero)
-- `Surreal.mk_div`
theorem c5_74 : ¬ indep0% Surreal.mk_div 3 := fun h =>
  not_numeric_star (@h 0 IGame.star Numeric.zero)
-- `IGame.Numeric.inv_nonneg`
theorem c5_75 : ¬ drop0% IGame.Numeric.inv_nonneg 1 := fun h => by
  have := (@h IGame.star).1 (by rw [starInv])
  exact absurd this (by game_cmp)
-- `IGame.Numeric.lt_div_iff`
theorem c5_76 : ¬ drop0% IGame.Numeric.lt_div_iff 3 := fun h => by
  have := (@h (-IGame.up + IGame.star) 0 2 Numeric.zero inferInstance (by game_cmp)).2
  rw [IGame.zero_div] at this
  refine absurd (this ?_) (by game_cmp)
  rw [← Game.mk_lt_mk, mkTwo, Game.mk_lt_mk]
  game_cmp
-- `IGame.Numeric.lt_div_iff'`
theorem c5_77 : ¬ drop0% IGame.Numeric.lt_div_iff' 3 := fun h => by
  have := (@h (-IGame.up + IGame.star) 0 2 Numeric.zero inferInstance (by game_cmp)).2
  rw [IGame.zero_div] at this
  refine absurd (this ?_) (by game_cmp)
  rw [mul_comm, ← Game.mk_lt_mk, mkTwo, Game.mk_lt_mk]
  game_cmp
-- `IGame.Numeric.lt_div_iff`
theorem c5_78 : ¬ drop0% IGame.Numeric.lt_div_iff 5 := fun h => by
  have := @h 1 1 IGame.up _ _ (by game_cmp)
  rw [IGame.div_eq_mul_inv, upInv, mul_one, one_mul] at this
  exact absurd (this.2 (by game_cmp)) (by game_cmp)
-- `IGame.Numeric.lt_div_iff'`
theorem c5_79 : ¬ drop0% IGame.Numeric.lt_div_iff' 5 := fun h => by
  have := @h 1 1 IGame.up _ _ (by game_cmp)
  rw [IGame.div_eq_mul_inv, upInv, mul_one, mul_one] at this
  exact absurd (this.2 (by game_cmp)) (by game_cmp)
-- `IGame.Numeric.div_lt_iff`
theorem c5_80 : ¬ drop0% IGame.Numeric.div_lt_iff 4 := fun h => by
  have := @h IGame.half IGame.up 1 _ _ (by game_cmp)
  rw [IGame.div_eq_mul_inv, upInv, mul_one, one_mul] at this
  exact absurd (this.1 (by game_cmp)) (by game_cmp)
-- `IGame.Numeric.div_lt_iff'`
theorem c5_81 : ¬ drop0% IGame.Numeric.div_lt_iff' 4 := fun h => by
  have := @h IGame.half IGame.up 1 _ _ (by game_cmp)
  rw [IGame.div_eq_mul_inv, upInv, mul_one, mul_one] at this
  exact absurd (this.1 (by game_cmp)) (by game_cmp)
-- `IGame.Numeric.div_lt_iff`
theorem c5_82 : ¬ drop0% IGame.Numeric.div_lt_iff 5 := fun h => by
  have := @h 1 2 (IGame.half + (IGame.up + IGame.star)) _ _ (by game_cmp)
  rw [IGame.div_eq_mul_inv, one_mul] at this
  exact nz (lt_of_le_of_lt twoInv.symm.le (this.2 zz))
-- `IGame.Numeric.div_lt_iff'`
theorem c5_83 : ¬ drop0% IGame.Numeric.div_lt_iff' 5 := fun h => by
  have := @h 1 2 (IGame.half + (IGame.up + IGame.star)) _ _ (by game_cmp)
  rw [IGame.div_eq_mul_inv, one_mul] at this
  exact nz (lt_of_le_of_lt twoInv.symm.le (this.2 (by rw [mul_comm]; exact zz)))
-- `IGame.Numeric.lt_div_iff_of_neg`
theorem c5_84 : ¬ drop0% IGame.Numeric.lt_div_iff_of_neg 5 := fun h => by
  have := @h (-1) IGame.half (-IGame.up) _ _ (by game_cmp)
  rw [IGame.div_eq_mul_inv, IGame.inv_neg, upInv, mul_neg, mul_one, neg_mul_neg, one_mul] at this
  exact absurd (this.1 (by game_cmp)) (by game_cmp)
-- `IGame.Numeric.div_lt_iff_of_neg`
theorem c5_85 : ¬ drop0% IGame.Numeric.div_lt_iff_of_neg 4 := fun h => by
  have := @h (-IGame.half) (-IGame.up) 1 _ _ (by game_cmp)
  rw [IGame.div_eq_mul_inv, IGame.inv_neg, upInv, mul_neg, mul_one, neg_neg, one_mul] at this
  exact absurd (this.1 (by game_cmp)) (by game_cmp)
-- `IGame.Numeric.div_lt_iff_of_neg`
theorem c5_86 : ¬ drop0% IGame.Numeric.div_lt_iff_of_neg 5 := fun h => by
  have := @h (-1) (-2) (IGame.half + (IGame.up + IGame.star)) _ _ (by game_cmp)
  rw [IGame.div_eq_mul_inv, IGame.inv_neg, neg_mul_neg, one_mul, mul_neg, IGame.neg_lt_neg_iff] at this
  exact nz (lt_of_le_of_lt twoInv.symm.le (this.2 zz))
-- `_private.CombinatorialGames.Surreal.Division.0.IGame.equiv_ratCast_of_mem_move_inv_natCast`
theorem c5_87 : ¬ drop0% _private.CombinatorialGames.Surreal.Division.«0».IGame.equiv_ratCast_of_mem_move_inv_natCast 3 := fun h => by
  obtain ⟨q, hq⟩ := @h 0 .left IGame.star
  exact notEqStar _ hq
-- `IGame.equiv_ratCast_of_mem_moves_left_ratCast`
theorem c5_88 : ¬ drop0% IGame.equiv_ratCast_of_mem_moves_left_ratCast 2 := fun h => by
  obtain ⟨q, _, hq⟩ := @h 0 IGame.star
  exact notEqStar _ hq
-- `IGame.equiv_ratCast_of_mem_moves_right_ratCast`
theorem c5_89 : ¬ drop0% IGame.equiv_ratCast_of_mem_moves_right_ratCast 2 := fun h => by
  obtain ⟨q, _, hq⟩ := @h 0 IGame.star
  exact notEqStar _ hq

namespace W2c5
open Surreal.Cut in
theorem sInfPos : sInf (leftSurreal '' Set.Ioi (0 : Surreal)) = rightSurreal 0 := by
  apply le_antisymm
  · by_contra hc
    rw [not_le] at hc
    obtain ⟨z, hz1, hz2⟩ := lt_iff_nonempty_inter.1 hc
    simp at hz1
    have h3 : sInf (leftSurreal '' Set.Ioi (0 : Surreal)) ≤ leftSurreal z := sInf_le ⟨z, hz1, rfl⟩
    have := left_subset_left_iff.2 h3 hz2
    simp at this
  · refine le_sInf ?_
    rintro _ ⟨y, hy, rfl⟩
    simpa using hy

open Surreal.Cut in
theorem sSupNeg : sSup (rightSurreal '' Set.Iio (0 : Surreal)) = leftSurreal 0 := by
  apply le_antisymm
  · refine sSup_le ?_
    rintro _ ⟨y, hy, rfl⟩
    rw [rightSurreal_le_iff]; simpa using hy
  · by_contra hc
    rw [not_le] at hc
    obtain ⟨z, hz1, hz2⟩ := lt_iff_nonempty_inter.1 hc
    simp at hz2
    have h3 : rightSurreal z ≤ sSup (rightSurreal '' Set.Iio (0 : Surreal)) := le_sSup ⟨z, hz2, rfl⟩
    have h4 := left_subset_left_iff.2 h3 (show z ∈ (rightSurreal z).left by simp)
    exact lt_irrefl z (Surreal.Cut.left_lt_right h4 hz1)
end W2c5

-- `Surreal.Cut.rightSurreal_mem_of_sInf_eq`
theorem c5_90 : ¬ drop0% Surreal.Cut.rightSurreal_mem_of_sInf_eq 2 := fun h => by
  obtain ⟨y, _, hy⟩ := @h _ 0 sInfPos
  exact Surreal.Cut.leftSurreal_ne_rightSurreal _ _ hy
-- `Surreal.Cut.leftSurreal_mem_of_sSup_eq`
theorem c5_91 : ¬ drop0% Surreal.Cut.leftSurreal_mem_of_sSup_eq 2 := fun h => by
  obtain ⟨y, _, hy⟩ := @h _ 0 sSupNeg
  exact Surreal.Cut.rightSurreal_ne_leftSurreal _ _ hy
-- `Dyadic.natAbs_num_div_den_upper_eq_natAbs_num_div_den`
theorem c5_92 : ¬ drop0% Dyadic.natAbs_num_div_den_upper_eq_natAbs_num_div_den 1 := fun h =>
  by
  have := @h 0
  first
  | exact absurd this (by decide +kernel)
  | (rw [Dyadic.upper_eq_of_den_eq_one (by first | rfl | simp)] at this; simp at this)
-- `IGame.Numeric.lt_div_iff`
theorem c5_93 : ¬ drop0% IGame.Numeric.lt_div_iff 6 := fun h => by
  have := @h (-1) (-1) 0 _ _ _
  simp only [IGame.div_eq_mul_inv, IGame.inv_zero, mul_zero] at this
  exact absurd (this.1 (by game_cmp)) (by game_cmp)
-- `IGame.Numeric.lt_div_iff'`
theorem c5_94 : ¬ drop0% IGame.Numeric.lt_div_iff' 6 := fun h => by
  have := @h (-1) (-1) 0 _ _ _
  simp only [IGame.div_eq_mul_inv, IGame.inv_zero, mul_zero, zero_mul] at this
  exact absurd (this.1 (by game_cmp)) (by game_cmp)

namespace W2c5
open IGame
theorem notNumUp' : ¬ Numeric IGame.up := fun hn =>
  not_numeric_star (Numeric.of_mem_moves (p := .right) (x := IGame.up) (by simp [IGame.up]))
end W2c5

open IGame W2c5

-- `Surreal.Cut.simplestBtwn_supLeft_infRight`
theorem c5_1 : ¬ indep0% Surreal.Cut.simplestBtwn_supLeft_infRight 1 := fun h => by
  have := @h IGame.star
  simp at this
-- `Surreal.Cut.simplestBtwn_leftGame_rightGame`
theorem c5_2 : ¬ indep0% Surreal.Cut.simplestBtwn_leftGame_rightGame 1 := fun h => by
  have := @h (Game.mk IGame.star)
  simp at this
-- `Surreal.Cut.supLeft_lt_infRight_of_equiv_numeric`
theorem c5_3 : ¬ drop0% Surreal.Cut.supLeft_lt_infRight_of_equiv_numeric 2 := fun h => by
  have := @h IGame.star IGame.star .rfl
  simp at this
-- `Surreal.Cut.supLeft_lt_infRight_of_equiv_numeric`
theorem c5_4 : ¬ drop0% Surreal.Cut.supLeft_lt_infRight_of_equiv_numeric 3 := fun h => by
  have := @h IGame.star 0 _
  simp at this
-- `Surreal.Cut.supLeft_lt_infRight_of_numeric`
theorem c5_5 : ¬ drop0% Surreal.Cut.supLeft_lt_infRight_of_numeric 1 := fun h => by
  have := h IGame.star
  simp at this
-- `Surreal.Cut.leftGame_eq_supLeft_of_le`
theorem c5_6 : ¬ drop0% Surreal.Cut.leftGame_eq_supLeft_of_le 1 := fun h =>
  Surreal.Cut.leftGame_ne_bot _ ((@h 0).trans (by simp [Surreal.Cut.supLeft]))
-- `Surreal.Cut.rightGame_eq_infRight_of_le`
theorem c5_7 : ¬ drop0% Surreal.Cut.rightGame_eq_infRight_of_le 1 := fun h =>
  Surreal.Cut.rightGame_ne_top _ ((@h 0).trans (by simp [Surreal.Cut.infRight]))
-- `Surreal.Cut.infRight_switch_le_supLeft_switch`
theorem c5_8 : ¬ drop0% Surreal.Cut.infRight_switch_le_supLeft_switch 1 := fun h => by
  have := @h (-1)
  simp at this
  exact (Surreal.Cut.rightSurreal_lt_leftSurreal_iff.2 (by norm_num)).not_ge this
-- `Surreal.Cut.leftGame_switch_of_numeric`
theorem c5_9 : ¬ indep0% Surreal.Cut.leftGame_switch_of_numeric 2 := fun h =>
  notNumUp' (@h IGame.up (by game_cmp))
-- `Surreal.Cut.birthday_simplestBtwn_le_of_fits`
theorem c5_10 : ¬ indep0% Surreal.Cut.birthday_simplestBtwn_le_of_fits 3 := fun h => by
  have := @h ⊤ ⊤ 0
  simp [Surreal.Cut.Fits] at this
-- `Surreal.Cut.Numeric.instNeg`
theorem c5_11 : ¬ drop0% Surreal.Cut.Numeric.instNeg 1 := fun h => by
  have := h ⊤
  simp at this
  exact Surreal.Cut.Numeric.ne_bot _ rfl
-- `Surreal.Cut.Numeric.instHVAdd`
theorem c5_12 : ¬ drop0% Surreal.Cut.Numeric.instHVAdd 2 := fun h => by
  have := h 0 ⊤
  rw [Surreal.Cut.vadd_top] at this
  exact Surreal.Cut.Numeric.ne_top _ rfl
-- `Surreal.Cut.mem_left_of_lt_toSurreal`
theorem c5_13 : ¬ indep0% Surreal.Cut.mem_left_of_lt_toSurreal 1 := fun h =>
  Surreal.Cut.Numeric.ne_top (hx := @h ⊤ 0) _ rfl
-- `Surreal.Cut.mem_right_of_toSurreal_lt`
theorem c5_14 : ¬ indep0% Surreal.Cut.mem_right_of_toSurreal_lt 1 := fun h =>
  Surreal.Cut.Numeric.ne_top (hx := @h ⊤ 0) _ rfl
-- `Surreal.Cut.toSurreal_neg`
theorem c5_15 : ¬ indep0% Surreal.Cut.toSurreal_neg 1 := fun h =>
  Surreal.Cut.Numeric.ne_top (hx := h ⊤) _ rfl
-- `Surreal.Cut.mem_left_of_lt_toSurreal`
theorem c5_16 : ¬ drop0% Surreal.Cut.mem_left_of_lt_toSurreal 3 := fun h => by
  have := @h (Surreal.Cut.leftSurreal 0) _ 0
  simp at this
