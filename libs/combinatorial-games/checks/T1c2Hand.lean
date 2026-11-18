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
namespace T1c2
open IGame Surreal

noncomputable abbrev two0 : IGame.{0} := ((2:ℕ):IGame)
theorem two0_left : two0ᴸ = {1} := by
  show ((Nat.succ 1 : ℕ) : IGame.{0})ᴸ = {1}; rw [moves_left_natCast_succ']; simp
theorem two0_right : two0ᴿ = ∅ := moves_right_natCast 2
theorem dTwo : ((2:Dyadic):IGame.{0}) = two0 := by simpa using Dyadic.toIGame_natCast 2

noncomputable abbrev Gs : IGame.{0} := ω^ (⋆ : IGame)
theorem Gs_nonneg : (0:IGame) ≤ Gs := by
  rw [le_iff_forall_lf]; refine ⟨by simp, ?_⟩
  intro b hb
  rw [moves_right_wpow] at hb
  obtain ⟨r, hr, z, hz, rfl⟩ := hb
  simp at hz; subst hz
  have : ((0:Dyadic):IGame.{0}) < r := Dyadic.toIGame_lt_toIGame.2 hr
  simp at this ⊢; first | exact this | exact this.not_ge
theorem one_mem_Gs : (1:IGame) ∈ Gsᴸ := by simp [moves_left_wpow]
theorem K : (1:IGame) ≤ two0 * Gs := by
  rw [le_iff_forall_lf]; constructor
  · intro z hz; simp at hz; subst hz
    rw [lf_iff_exists_le]; left
    refine ⟨mulOption two0 Gs 1 0, mulOption_mem_moves_mul (px := .left) (py := .left) (by simp [two0_left]) (zero_mem_moves_left_wpow _), ?_⟩
    simp [mulOption, Gs_nonneg]
  · intro z hz
    rw [moves_mul] at hz
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := hz
    simp [two0_left, two0_right] at hab
    obtain ⟨rfl, hb⟩ := hab
    rw [moves_right_wpow] at hb
    obtain ⟨r, hr, z, hz, rfl⟩ := hb
    simp at hz; subst hz
    rw [lf_iff_exists_le]; left
    simp only [IGame.wpow_zero, mul_one]
    refine ⟨(1 + two0 * r) - 1 * r, ?_, ?_⟩
    · rw [moves_mulOption]
      rw [moves_sub]; left
      exact ⟨_, add_right_mem_moves_add (by rw [one_mul]; exact one_mem_Gs) _, rfl⟩
    · have hr' : (0:ℚ) < r := by exact_mod_cast hr
      rw [← Surreal.mk_le_mk]; simp
      have e : Surreal.mk (2:IGame.{0}) = 2 := Surreal.mk_natCast 2
      rw [e]
      have : (0:Surreal.{0}) < ((r:ℚ):Surreal.{0}) := by exact_mod_cast hr'
      linarith

noncomputable abbrev hD : Dyadic := Dyadic.half
noncomputable abbrev q4 : Dyadic := hD * hD
theorem q4_mem : (q4:IGame.{0}) ∈ Gsᴿ := by
  have := mul_wpow_mem_moves_right_wpow (x := ⋆) (r := q4) (by decide) (y := 0) (by simp)
  simpa using this
theorem m2_mem (s : ℝ) (hs : -2 < s) : (-two0 : IGame.{0}) ∈ (s:IGame.{0})ᴸ := by
  rw [Real.moves_left_toIGame]; refine ⟨-2, ?_, ?_⟩
  · simp; norm_num; linarith
  · rw [Dyadic.toIGame_neg, dTwo]

-- For real s > -2: the right option (-2)·Gs + s·¼ + 2·¼ of s·ω^ ⋆, plus d, is ≤ c
theorem ropt_le (s : ℝ) (hs : -2 < s) (d c : IGame.{0}) [Numeric d] [Numeric c]
    (h : Surreal.mk d + s / 4 + 1 / 2 ≤ 1 + Surreal.mk c) :
    ∃ R ∈ ((s:IGame.{0}) * Gs)ᴿ, R + d ≤ c := by
  refine ⟨_, mulOption_mem_moves_mul (px := .left) (py := .right) (m2_mem s hs) q4_mem, ?_⟩
  simp only [mulOption, neg_mul]
  rw [← Game.mk_le_mk]
  have hN : Game.mk ((s:IGame.{0}) * q4 + two0 * q4 + d) ≤ Game.mk (1 + c) := by
    rw [← Surreal.toGame_mk, ← Surreal.toGame_mk, Surreal.toGame_le_iff]
    simp
    rw [show Surreal.mk (2:IGame.{0}) = 2 from Surreal.mk_natCast 2]
    linarith
  have hK := Game.mk_le_mk.2 K
  simp only [Game.mk_add, Game.mk_sub, Game.mk_neg] at hN ⊢
  calc _ = (Game.mk ((s:IGame.{0}) * q4) + Game.mk (two0 * q4) + Game.mk d) - Game.mk (two0 * Gs) := by abel
    _ ≤ (Game.mk 1 + Game.mk c) - Game.mk 1 := sub_le_sub hN hK
    _ = Game.mk c := by abel

-- `IGame.Numeric.mul_wpow_lt_mul_wpow_of_pos` idx 3: necessary (x = -1, y = ⋆, r = 0, s = 1)
theorem t1c2_5 : ¬ drop0% IGame.Numeric.mul_wpow_lt_mul_wpow_of_pos 3 := fun h => by
  have := @h (-1) ⋆ _ 0 1 one_pos (by game_cmp)
  obtain ⟨R, hR, hle⟩ := ropt_le 1 (by norm_num) 0 ((0:ℝ) * ω^ (-1:IGame.{0})) (by simp; norm_num)
  rw [add_zero] at hle
  exact (lf_iff_exists_le.2 (Or.inr ⟨R, hR, hle⟩)) this.le
-- `IGame.Numeric.wpow_lt_mul_wpow` idx 3: necessary (x = -1, y = ⋆, r = 1)
theorem t1c2_6 : ¬ drop0% IGame.Numeric.wpow_lt_mul_wpow 3 := fun h => by
  have := @h (-1) ⋆ _ 1 one_pos (by game_cmp)
  obtain ⟨R, hR, hle⟩ := ropt_le 1 (by norm_num) 0 (ω^ (-1:IGame.{0})) (by have : (0:Surreal.{0}) ≤ (ω^ (1:Surreal.{0}))⁻¹ := inv_nonneg.2 (Surreal.wpow_nonneg _); simp; norm_num; linarith)
  rw [add_zero] at hle
  exact (lf_iff_exists_le.2 (Or.inr ⟨R, hR, hle⟩)) this.le
-- `IGame.Numeric.mul_wpow_lt_mul_wpow_add_mul_wpow` idx 4: necessary (x = -1, y = ⋆, z = 0, r = 0, s = 1, t = 1/4)
theorem t1c2_7 : ¬ drop0% IGame.Numeric.mul_wpow_lt_mul_wpow_add_mul_wpow 4 := fun h => by
  have := @h (-1) ⋆ 0 _ _ 0 1 (1/4) one_pos (by norm_num) (by game_cmp) (by game_cmp)
  rw [IGame.wpow_zero, mul_one] at this
  obtain ⟨R, hR, hle⟩ := ropt_le 1 (by norm_num) (((1/4:ℝ)):IGame.{0}) ((0:ℝ) * ω^ (-1:IGame.{0})) (by simp; norm_num)
  exact (lf_iff_exists_le.2 (Or.inr ⟨R + _, add_right_mem_moves_add hR _, hle⟩)) this.le
-- `IGame.Numeric.mul_wpow_lt_mul_wpow_add_mul_wpow` idx 5: necessary (x = -1, y = 0, z = ⋆, r = 0, s = 1/4, t = 1)
theorem t1c2_8 : ¬ drop0% IGame.Numeric.mul_wpow_lt_mul_wpow_add_mul_wpow 5 := fun h => by
  have := @h (-1) 0 ⋆ _ _ 0 (1/4) 1 (by norm_num) one_pos (by game_cmp) (by game_cmp)
  rw [IGame.wpow_zero, mul_one] at this
  obtain ⟨R, hR, hle⟩ := ropt_le 1 (by norm_num) (((1/4:ℝ)):IGame.{0}) ((0:ℝ) * ω^ (-1:IGame.{0})) (by simp; norm_num)
  exact (lf_iff_exists_le.2 (Or.inr ⟨_ + R, add_left_mem_moves_add hR _, by rw [add_comm]; exact hle⟩)) this.le
-- `IGame.Numeric.mul_wpow_add_mul_wpow_lt_mul_wpow` idx 5: necessary (x = y = -1, z = ⋆, r = s = 0, t = 1)
theorem t1c2_9 : ¬ drop0% IGame.Numeric.mul_wpow_add_mul_wpow_lt_mul_wpow 5 := fun h => by
  have := @h (-1) (-1) ⋆ _ _ 0 0 1 one_pos (by game_cmp) (by game_cmp)
  obtain ⟨R, hR, hle⟩ := ropt_le 1 (by norm_num) 0 ((0:ℝ) * ω^ (-1:IGame.{0}) + (0:ℝ) * ω^ (-1:IGame.{0})) (by simp; norm_num)
  rw [add_zero] at hle
  exact (lf_iff_exists_le.2 (Or.inr ⟨R, hR, hle⟩)) this.le

theorem two_mem_R (r : ℝ) (hr : r < 2) : (two0 : IGame.{0}) ∈ (r:IGame.{0})ᴿ := by
  rw [Real.moves_right_toIGame]; exact ⟨2, by simpa using hr, dTwo⟩
-- For real -2 ≤ r < 2: 0 ⧏ r·ω^ ⋆ (left option 2·Gs + r·¼ − 2·¼ ≥ 0)
theorem lf_RGs (r : ℝ) (hr : r < 2) (hr' : -2 ≤ r) : (0:IGame) ⧏ (r:IGame.{0}) * Gs := by
  refine lf_of_le_left ?_ (mulOption_mem_moves_mul (px := .right) (py := .right) (two_mem_R r hr) q4_mem)
  simp only [mulOption]
  rw [← Game.mk_le_mk]
  have hN : Game.mk (0:IGame.{0}) ≤ Game.mk ((r:IGame.{0}) * q4 - two0 * q4 + 1) := by
    rw [← Surreal.toGame_mk, ← Surreal.toGame_mk, Surreal.toGame_le_iff]
    simp
    rw [show Surreal.mk (2:IGame.{0}) = 2 from Surreal.mk_natCast 2]
    have : ((-2:ℝ):Surreal.{0}) ≤ (r:Surreal.{0}) := Real.toSurreal_le_iff.2 hr'
    simp at this
    linarith
  have hK := Game.mk_le_mk.2 K
  simp only [Game.mk_add, Game.mk_sub, Game.mk_zero] at hN ⊢
  calc (0:Game) ≤ Game.mk ((r:IGame.{0}) * q4) - Game.mk (two0 * q4) + Game.mk 1 := hN
    _ ≤ Game.mk ((r:IGame.{0}) * q4) - Game.mk (two0 * q4) + Game.mk (two0 * Gs) := add_le_add_right hK _
    _ = _ := by abel

-- `IGame.Numeric.mul_wpow_lt_mul_wpow_of_neg` idx 2: necessary (x = ⋆, y = -1, r = s = -1)
theorem t1c2_10 : ¬ drop0% IGame.Numeric.mul_wpow_lt_mul_wpow_of_neg 2 := fun h => by
  have := @h ⋆ (-1) _ (-1) (-1) (by norm_num) (by game_cmp)
  have h0 : ((-1:ℝ):IGame.{0}) * ω^ (-1:IGame.{0}) ≤ 0 := by
    rw [← Surreal.mk_le_mk]; simp
  exact lf_RGs (-1) (by norm_num) (by norm_num) (this.le.trans h0)
noncomputable abbrev Ys : IGame.{0} := !{{⋆} | ∅}
theorem mkTwo : Surreal.mk (2:IGame.{0}) = 2 := Surreal.mk_natCast 2
theorem mkThree : Surreal.mk (3:IGame.{0}) = 3 := Surreal.mk_natCast 3
theorem two_mem_Gs : (2:IGame.{0}) ∈ Gsᴸ := by
  simp [moves_left_wpow]; exact ⟨2, by decide, by simpa using Dyadic.toIGame_natCast 2⟩
theorem monoS {a a' b c d e : IGame} (h : a ≤ a') : a + b - c + d - e ≤ a' + b - c + d - e := by
  simp only [sub_eq_add_neg]
  exact add_le_add_left (add_le_add_left (add_le_add_left (add_le_add_left h _) _) _) _
theorem stepQ (k : ℕ) (h0 : (k:IGame.{0}) ≤ ((k+1:ℕ):IGame) * Gs) (h1 : ((k+1:ℕ):IGame.{0}) ≤ ((k+2:ℕ):IGame) * Gs) :
    ((k+2:ℕ):IGame.{0}) ≤ ((k+3:ℕ):IGame) * Gs := by
  rw [le_iff_forall_lf]; constructor
  · intro z hz
    have e : ((k+2:ℕ):IGame.{0})ᴸ = {((k+1:ℕ):IGame)} := moves_left_natCast_succ' (k+1)
    rw [e] at hz
    simp only [Set.mem_singleton_iff] at hz; subst hz
    rw [lf_iff_exists_le]; left
    refine ⟨mulOption ((k+3:ℕ):IGame) Gs ((k+2:ℕ):IGame) 0,
      mulOption_mem_moves_mul (px := .left) (py := .left) ?_ (zero_mem_moves_left_wpow _), ?_⟩
    · have e : ((k+3:ℕ):IGame.{0})ᴸ = {((k+2:ℕ):IGame)} := moves_left_natCast_succ' (k+2)
      rw [e]; rfl
    · simp only [mulOption, mul_zero, add_zero, sub_zero]; exact h1
  · intro z hz
    rw [moves_mul] at hz
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := hz
    simp only [Player.neg_right, Set.mem_union, Set.mem_prod, moves_right_natCast, Set.mem_empty_iff_false,
      false_and, or_false] at hab
    obtain ⟨ha, hb⟩ := hab
    have e : ((k+3:ℕ):IGame.{0})ᴸ = {((k+2:ℕ):IGame)} := moves_left_natCast_succ' (k+2)
    rw [e, Set.mem_singleton_iff] at ha
    subst ha
    rw [moves_right_wpow] at hb
    obtain ⟨r, hr, w, hw, rfl⟩ := hb
    simp at hw; subst hw
    simp only [IGame.wpow_zero, mul_one]
    rw [lf_iff_exists_le]; left
    refine ⟨mulOption ((k+2:ℕ):IGame) Gs ((k+1:ℕ):IGame) 2 + ((k+3:ℕ):IGame) * r - ((k+2:ℕ):IGame) * r, ?_, ?_⟩
    · rw [moves_mulOption, moves_sub]; left
      refine ⟨_, add_right_mem_moves_add (mulOption_mem_moves_mul (px := .left) (py := .left) ?_ two_mem_Gs) _, rfl⟩
      have e : ((k+2:ℕ):IGame.{0})ᴸ = {((k+1:ℕ):IGame)} := moves_left_natCast_succ' (k+1)
      rw [e]; rfl
    · unfold mulOption
      refine le_trans ?_ (monoS (b := ((k+2:ℕ):IGame) * 2) (c := ((k+1:ℕ):IGame) * 2)
        (d := ((k+3:ℕ):IGame) * r) (e := ((k+2:ℕ):IGame) * r) h0)
      have hr' : (0:ℚ) < r := by exact_mod_cast hr
      rw [← Surreal.mk_le_mk]; simp [mkTwo, mkThree]
      have : (0:Surreal.{0}) < ((r:ℚ):Surreal.{0}) := by exact_mod_cast hr'
      push_cast; linarith
theorem allQ : ∀ n : ℕ, (n:IGame.{0}) ≤ ((n+1:ℕ):IGame) * Gs ∧ ((n+1:ℕ):IGame.{0}) ≤ ((n+2:ℕ):IGame) * Gs
  | 0 => ⟨by simpa using Gs_nonneg, by simpa using K⟩
  | n+1 => ⟨(allQ n).2, stepQ n (allQ n).1 (allQ n).2⟩
theorem w1_le_wY : ω^ (1:IGame.{0}) ≤ ω^ Ys := by
  rw [le_iff_forall_lf]; constructor
  · intro z hz
    rw [moves_left_wpow] at hz
    rcases hz with rfl | ⟨r, hr, w, hw, rfl⟩
    · exact zero_lf_wpow _
    · simp at hw; subst hw
      simp only [IGame.wpow_zero, mul_one]
      obtain ⟨n, hn⟩ : ∃ n : ℕ, (r:ℚ) ≤ n := ⟨_, Nat.le_ceil _⟩
      have hle : (r:IGame.{0}) ≤ (n:IGame) := by
        rw [← Surreal.mk_le_mk]; simp; exact_mod_cast hn
      refine lf_of_le_left (hle.trans (allQ n).1) ?_
      have hm : (((n+1:ℕ):Dyadic):IGame.{0}) * ω^ ⋆ ∈ (ω^ Ys)ᴸ :=
        mul_wpow_mem_moves_left_wpow (by positivity) (by simp)
      rw [Dyadic.toIGame_natCast] at hm; exact hm
  · intro z hz; simp [moves_right_wpow] at hz

theorem Ys_lt_one : Ys < 1 := by game_cmp

noncomputable abbrev H : IGame.{0} := ω^ Ys
-- for real r > 1: r·ω^ Ys has the left option ω^ Ys (q = 1, option 0)
theorem H_mem_RH (r : ℝ) (hr : 1 < r) : H ∈ ((r:IGame.{0}) * H)ᴸ := by
  have h1 : ((1:Dyadic):IGame.{0}) ∈ (r:IGame.{0})ᴸ := by
    rw [Real.moves_left_toIGame]; exact ⟨1, by simpa using hr, rfl⟩
  have := mulOption_mem_moves_mul (px := .left) (py := .left) h1 (zero_mem_moves_left_wpow Ys)
  simpa [mulOption] using this
-- for real r < -1: r·ω^ Ys has the right option -ω^ Ys
theorem negH_mem_RH (r : ℝ) (hr : r < -1) : -H ∈ ((r:IGame.{0}) * H)ᴿ := by
  have h1 : ((-1:Dyadic):IGame.{0}) ∈ (r:IGame.{0})ᴿ := by
    rw [Real.moves_right_toIGame]; exact ⟨-1, by simpa using hr, rfl⟩
  have := mulOption_mem_moves_mul (px := .right) (py := .left) h1 (zero_mem_moves_left_wpow Ys)
  simpa [mulOption] using this
theorem R1w (s : ℝ) (hs : s ≤ 1) : (s:IGame.{0}) * ω^ (1:IGame.{0}) ≤ H := by
  refine le_trans ?_ w1_le_wY
  rw [← Surreal.mk_le_mk]; simp
  have : (s:Surreal.{0}) ≤ 1 := by simpa using (Real.toSurreal_le_iff.2 hs)
  have h0 : (0:Surreal.{0}) ≤ ω^ (1:Surreal.{0}) := Surreal.wpow_nonneg _
  nlinarith

-- `IGame.Numeric.mul_wpow_lt_mul_wpow_of_pos` idx 2: necessary (x = {⋆|} < 1 = y, r = 2, s = 1: ω^ 1 ≤ ω^ x is a left option of 2·ω^ x)
theorem t1c2_11 : ¬ drop0% IGame.Numeric.mul_wpow_lt_mul_wpow_of_pos 2 := fun h => by
  have := @h Ys 1 _ 2 1 one_pos Ys_lt_one
  exact lf_of_le_left (R1w 1 le_rfl) (H_mem_RH 2 (by norm_num)) this.le
-- `IGame.Numeric.mul_wpow_lt_wpow` idx 2: necessary (x = {⋆|} < 1 = y, r = 2)
theorem t1c2_12 : ¬ drop0% IGame.Numeric.mul_wpow_lt_wpow 2 := fun h => by
  have := @h Ys 1 _ 2 Ys_lt_one
  exact lf_of_le_left w1_le_wY (H_mem_RH 2 (by norm_num)) this.le
-- `IGame.Numeric.mul_wpow_lt_mul_wpow_add_mul_wpow` idx 3: necessary (x = {⋆|}, y = z = 1, r = 2, s = t = 1/2)
theorem t1c2_13 : ¬ drop0% IGame.Numeric.mul_wpow_lt_mul_wpow_add_mul_wpow 3 := fun h => by
  have := @h Ys 1 1 _ _ 2 (1/2) (1/2) (by norm_num) (by norm_num) Ys_lt_one Ys_lt_one
  refine lf_of_le_left (le_trans ?_ w1_le_wY) (H_mem_RH 2 (by norm_num)) this.le
  rw [← Surreal.mk_le_mk]; simp; ring_nf; rfl
-- `IGame.Numeric.mul_wpow_add_mul_wpow_lt_mul_wpow` idx 3: necessary (x = {⋆|}, y = 0, z = 1, r = 2, s = 0, t = 1)
theorem t1c2_14 : ¬ drop0% IGame.Numeric.mul_wpow_add_mul_wpow_lt_mul_wpow 3 := fun h => by
  have := @h Ys 0 1 _ _ 2 0 1 one_pos Ys_lt_one (by game_cmp)
  refine lf_of_le_left ?_ (add_right_mem_moves_add (H_mem_RH 2 (by norm_num)) _) this.le
  rw [← Game.mk_le_mk, Game.mk_add]
  have e : Game.mk ((0:ℝ) * ω^ (0:IGame.{0})) = 0 := by simp
  rw [e, add_zero, Game.mk_le_mk]; exact R1w 1 le_rfl
-- `IGame.Numeric.mul_wpow_add_mul_wpow_lt_mul_wpow` idx 4: necessary (x = 0, y = {⋆|}, z = 1, r = 0, s = 2, t = 1)
theorem t1c2_15 : ¬ drop0% IGame.Numeric.mul_wpow_add_mul_wpow_lt_mul_wpow 4 := fun h => by
  have := @h 0 Ys 1 _ _ 0 2 1 one_pos (by game_cmp) Ys_lt_one
  refine lf_of_le_left ?_ (add_left_mem_moves_add (H_mem_RH 2 (by norm_num)) _) this.le
  rw [← Game.mk_le_mk, Game.mk_add]
  have e : Game.mk ((0:ℝ) * ω^ (0:IGame.{0})) = 0 := by simp
  rw [e, zero_add, Game.mk_le_mk]; exact R1w 1 le_rfl
-- `IGame.Numeric.mul_wpow_lt_mul_wpow_of_neg` idx 3: necessary (x = 1, y = {⋆|}, r = -1, s = -2: right option -ω^ y of s·ω^ y is ≤ -ω)
theorem t1c2_16 : ¬ drop0% IGame.Numeric.mul_wpow_lt_mul_wpow_of_neg 3 := fun h => by
  have := @h 1 Ys _ (-1) (-2) (by norm_num) Ys_lt_one
  refine (lf_iff_exists_le.2 (Or.inr ⟨_, negH_mem_RH (-2) (by norm_num), ?_⟩)) this.le
  rw [← Game.mk_le_mk, Game.mk_neg]
  have e : Game.mk (((-1:ℝ):IGame.{0}) * ω^ (1:IGame.{0})) = -Game.mk (ω^ (1:IGame.{0})) := by
    rw [← Surreal.toGame_mk, ← Surreal.toGame_mk]; simp
  rw [e, neg_le_neg_iff, Game.mk_le_mk]; exact w1_le_wY

-- R0 = real 0 as a game
noncomputable abbrev R0 : IGame.{0} := ((0:ℝ):IGame)

-- 0 ⧏ R0 * Gs: left option 2·Gs + R0·½ − 2·½ ≥ 0
theorem zero_lf_R0Gs : (0:IGame) ⧏ R0 * Gs := by
  have h2 : (two0 : IGame) ∈ R0ᴿ := by
    rw [Real.moves_right_toIGame]; exact ⟨2, by simp, dTwo⟩
  have hh : ((hD:IGame) * ω^ (0:IGame)) ∈ Gsᴿ :=
    mul_wpow_mem_moves_right_wpow (by decide) (by simp)
  refine lf_of_le_left ?_ (mulOption_mem_moves_mul (px := .right) (py := .right) h2 hh)
  simp only [IGame.wpow_zero, mul_one, mulOption]
  have hB : R0 * (hD:IGame) ≈ 0 := by
    rw [← Surreal.mk_eq_mk]; simp
  have hC : two0 * (hD:IGame) ≈ 1 := by
    rw [← Surreal.mk_eq_mk]; simp
    rw [show Surreal.mk (2:IGame.{0}) = 2 from Surreal.mk_natCast 2]; norm_num
  rw [← Game.mk_le_mk]
  simp only [Game.mk_sub, Game.mk_add, Game.mk_zero]
  rw [Game.mk_eq hB, Game.mk_eq hC]
  have := Game.mk_le_mk.2 K
  rw [Game.mk_zero, add_zero, sub_nonneg]; exact this

-- Real-coefficient sum: RHS of realCast_mul_wpow_equiv at r = 0, x = ⋆ is ≤ 0
theorem rhs_le : !{(fun s : ℝ ↦ (s:IGame.{0}) * Gs) '' Set.Iio 0 | (fun s : ℝ ↦ (s:IGame.{0}) * Gs) '' Set.Ioi 0} ≤ 0 := by
  rw [le_iff_forall_lf]; refine ⟨?_, by simp⟩
  intro L hL
  simp only [moves_left_ofSets, Set.mem_image, Set.mem_Iio] at hL
  obtain ⟨s, hs, rfl⟩ := hL
  rw [lf_iff_exists_le]; right
  have h0 : ((0:Dyadic):IGame.{0}) ∈ (s:IGame.{0})ᴿ := by
    rw [Real.moves_right_toIGame]; exact ⟨0, by simpa using hs, rfl⟩
  refine ⟨mulOption (s:IGame.{0}) Gs ((0:Dyadic):IGame) 0,
    mulOption_mem_moves_mul (px := .right) (py := .left) h0 (zero_mem_moves_left_wpow _), ?_⟩
  simp [mulOption]

-- `IGame.Numeric.realCast_mul_wpow_equiv` idx 2: necessary (r = 0, x = ⋆)
theorem t1c2_1 : ¬ drop0% IGame.Numeric.realCast_mul_wpow_equiv 2 := fun h => by
  have := (@h 0 ⋆).1
  exact zero_lf_R0Gs (this.trans rhs_le)
-- `IGame.Numeric.wpow_mul_realCast_equiv` idx 2: necessary (r = 0, x = ⋆)
theorem t1c2_2 : ¬ drop0% IGame.Numeric.wpow_mul_realCast_equiv 2 := fun h => by
  have := (@h 0 ⋆).1
  simp only [mul_comm (ω^ (⋆:IGame.{0}))] at this
  exact zero_lf_R0Gs (this.trans rhs_le)

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
theorem Gs_pos : (0:IGame) < Gs := lt_of_le_not_ge Gs_nonneg (zero_lf_wpow _)
theorem one_mem_GsR : (1:IGame) ∈ Gsᴿ := by
  have := mul_wpow_mem_moves_right_wpow (x := ⋆) (r := 1) (by decide) (y := 0) (by simp)
  simpa using this
theorem one_mem_GsInv : (1:IGame.{0}) ∈ Gs⁻¹ᴸ := by
  have := invOption_mem_moves_inv (p₁ := .left) (p₂ := .left) (y := 1) Gs_pos (by game_cmp) (by simpa using one_mem_GsR) (zero_mem_moves_left_inv Gs_pos)
  simpa [invOption, IGame.div_eq_mul_inv, oneInv] using this
theorem b_mem_GsInv : (1 + (1 - Gs)) ∈ Gs⁻¹ᴿ := by
  have := invOption_mem_moves_inv (p₁ := .left) (p₂ := .right) (y := 1) Gs_pos (by game_cmp) (by simpa using one_mem_Gs) one_mem_GsInv
  simpa [invOption, IGame.div_eq_mul_inv, oneInv] using this
theorem two_le_GsGs : (1 + 1 : IGame.{0}) ≤ Gs + Gs := by
  rw [le_iff_forall_lf]; constructor
  · intro z hz
    rw [moves_add] at hz
    have hz1 : z = 1 := by rcases hz with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ <;> simp at ha <;> simp [ha]
    subst hz1
    refine lf_of_le_left ?_ (add_right_mem_moves_add one_mem_Gs Gs)
    simpa using Gs_nonneg
  · intro z hz
    rw [moves_add] at hz
    rcases hz with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · refine lf_of_le_left ?_ (add_left_mem_moves_add two_mem_Gs a)
      rw [moves_right_wpow] at ha
      obtain ⟨r, hr, w, hw, rfl⟩ := ha
      simp at hw; subst hw
      simp only [IGame.wpow_zero, mul_one]
      have hr' : (0:ℚ) < r := by exact_mod_cast hr
      rw [← Surreal.mk_le_mk]; simp
      rw [show Surreal.mk (2:IGame.{0}) = 2 from Surreal.mk_natCast 2]
      have : (0:Surreal.{0}) < ((r:ℚ):Surreal.{0}) := by exact_mod_cast hr'
      linarith
    · refine lf_of_le_left ?_ (add_right_mem_moves_add two_mem_Gs a)
      rw [moves_right_wpow] at ha
      obtain ⟨r, hr, w, hw, rfl⟩ := ha
      simp at hw; subst hw
      simp only [IGame.wpow_zero, mul_one]
      have hr' : (0:ℚ) < r := by exact_mod_cast hr
      rw [← Surreal.mk_le_mk]; simp
      rw [show Surreal.mk (2:IGame.{0}) = 2 from Surreal.mk_natCast 2]
      have : (0:Surreal.{0}) < ((r:ℚ):Surreal.{0}) := by exact_mod_cast hr'
      linarith
theorem b_le_Gs : 1 + (1 - Gs) ≤ Gs := by
  rw [← Game.mk_le_mk]
  have := Game.mk_le_mk.2 two_le_GsGs
  simp only [Game.mk_add, Game.mk_sub] at this ⊢
  have e : Game.mk 1 + (Game.mk 1 - Game.mk Gs) = (Game.mk 1 + Game.mk 1) - Game.mk Gs := by abel
  rw [e, sub_le_iff_le_add]; exact this
theorem not_Gs_le_inv : ¬ Gs ≤ Gs⁻¹ := fun h =>
  (lf_iff_exists_le.2 (Or.inr ⟨_, b_mem_GsInv, b_le_Gs⟩)) h

-- `IGame.Numeric.wpow_neg_equiv` idx 1: necessary (x = ⋆: ω^ ⋆ has the right option 1 + (1 − ω^ ⋆) of its inverse below it)
theorem t1c2_3 : ¬ drop0% IGame.Numeric.wpow_neg_equiv 1 := fun h => by
  have := (@h ⋆).1
  simp only [IGame.neg_star] at this
  exact not_Gs_le_inv this
-- `IGame.Numeric.wpow_sub_equiv` idx 3: necessary (x = 0, y = ⋆)
theorem t1c2_4 : ¬ drop0% IGame.Numeric.wpow_sub_equiv 3 := fun h => by
  have := (@h 0 ⋆ _).1
  simp only [sub_eq_add_neg, zero_add, IGame.neg_star, IGame.wpow_zero, IGame.div_eq_mul_inv, one_mul] at this
  exact not_Gs_le_inv this


noncomputable abbrev Wm : IGame.{0} := ω^ ((-1:IGame.{0}) + ⋆)
-- ω^ (-1 + ⋆) ≤ 1: its left options are 0 and r·ω^ -1
theorem Wm_le : Wm ≤ 1 := by
  rw [le_iff_forall_lf]; refine ⟨?_, by simp⟩
  rw [forall_mem_moves_left_wpow]
  refine ⟨by game_cmp, ?_⟩
  intro r hr y hy
  simp at hy; subst hy
  have := Numeric.mul_wpow_lt_wpow' (x := (-1:IGame.{0})) (y := 0) r (by game_cmp)
  rw [IGame.wpow_zero] at this
  exact this.not_ge
theorem three_mem_eps : (3:IGame.{0}) ∈ (ω^ (-1:IGame.{0}))ᴿ := by
  have := mul_wpow_mem_moves_right_wpow (x := (-1:IGame.{0})) (r := 3) (by decide) (y := 0) (by simp)
  have e : ((3:Dyadic):IGame.{0}) = 3 := Dyadic.toIGame_natCast 3
  rw [e, IGame.wpow_zero, mul_one] at this; exact this
theorem two_le_3Gs : (2:IGame.{0}) ≤ 3 * Gs := by
  have := (allQ 1).2; norm_num at this; exact this
-- the left option 3·ω^ ⋆ + ω^ -1·¼ − 3·¼ of ω^ -1 · ω^ ⋆ is ≥ 1
theorem one_le_L : (1:IGame.{0}) ≤ mulOption (ω^ (-1:IGame.{0})) Gs 3 q4 := by
  simp only [mulOption]
  rw [← Game.mk_le_mk]
  have hN : Game.mk (1:IGame.{0}) ≤ Game.mk (ω^ (-1:IGame.{0}) * q4 - 3 * q4 + 2) := by
    rw [← Surreal.toGame_mk, ← Surreal.toGame_mk, Surreal.toGame_le_iff]
    have : (0:Surreal.{0}) ≤ (ω^ (1:Surreal.{0}))⁻¹ := inv_nonneg.2 (Surreal.wpow_nonneg _)
    simp
    rw [show Surreal.mk (2:IGame.{0}) = 2 from Surreal.mk_natCast 2,
      show Surreal.mk (3:IGame.{0}) = 3 from Surreal.mk_natCast 3]
    norm_num
    nlinarith
  have hK := Game.mk_le_mk.2 two_le_3Gs
  simp only [Game.mk_add, Game.mk_sub] at hN ⊢
  calc Game.mk 1 ≤ Game.mk (ω^ (-1:IGame.{0}) * q4) - Game.mk (3 * q4) + Game.mk 2 := hN
    _ ≤ Game.mk (ω^ (-1:IGame.{0}) * q4) - Game.mk (3 * q4) + Game.mk (3 * Gs) := add_le_add_right hK _
    _ = _ := by abel
theorem not_epsGs_le : ¬ (ω^ (-1:IGame.{0}) * Gs ≤ Wm) :=
  lf_of_le_left (Wm_le.trans one_le_L)
    (mulOption_mem_moves_mul (px := .right) (py := .right) three_mem_eps q4_mem)

-- `IGame.Numeric.wpow_add_equiv` idx 3: necessary (x = -1, y = ⋆: ω^ (-1 + ⋆) ≤ 1, but ω^ -1 · ω^ ⋆ has the left option 3·ω^ ⋆ + ω^ -1·¼ − 3·¼ ≥ 1)
theorem t1c2_17 : ¬ drop0% IGame.Numeric.wpow_add_equiv 3 := fun h =>
  not_epsGs_le (@h (-1) ⋆ _).2
-- `IGame.Numeric.wpow_add_equiv` idx 2: necessary (x = ⋆, y = -1; commuted)
theorem t1c2_18 : ¬ drop0% IGame.Numeric.wpow_add_equiv 2 := fun h => by
  have := (@h ⋆ (-1) _).2
  rw [mul_comm, add_comm] at this
  exact not_epsGs_le this
end T1c2
