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

namespace W1c4
theorem on_win : LGame.IsWin Player.left LGame.on :=
  LGame.IsWin.intro (y := LGame.on) (by simp) (LGame.IsLoss.intro (fun y hy => by simp at hy))
theorem zero_loss (p : Player) : LGame.IsLoss p 0 := LGame.IsLoss.intro (fun y hy => by simp at hy)
theorem zero_not_win (p : Player) : ¬ LGame.IsWin p 0 := LGame.not_isWin_of_isLoss (zero_loss p)
end W1c4

-- `LGame.IsLoss.isWin_of_mem_moves` idx 3: necessary (x = y = dud)
theorem w4_1 : ¬ drop0% LGame.IsLoss.isWin_of_mem_moves 3 := fun h =>
  (LGame.isDraw_dud _).not_isWin (@h Player.left LGame.dud LGame.dud (by simp))
-- `LGame.IsLoss.isWin_of_mem_moves` idx 4: necessary (x = y = 0)
theorem w4_2 : ¬ drop0% LGame.IsLoss.isWin_of_mem_moves 4 := fun h =>
  W1c4.zero_not_win _ (@h Player.left 0 0 (W1c4.zero_loss _))
-- `LGame.IsStrategy.neg` idx 2: necessary (p = right, s = {1})
theorem w4_3 : ¬ drop0% LGame.IsStrategy.neg 2 := fun h => by
  have := @h Player.right {1}
  obtain ⟨r, hr, -⟩ := this (-1) (by simp) 0 (by simp [LGame.moves_neg])
  simp at hr
-- `LGame.IsStrategy.iUnion` idx 3: necessary (p = right, s = {1})
theorem w4_4 : ¬ drop0% LGame.IsStrategy.iUnion 3 := fun h => by
  have := @h Player.right True (fun _ => {1})
  obtain ⟨r, hr, -⟩ := this 1 (by simp) 0 (by simp)
  simp at hr
-- `LGame.IsStrategy.sUnion` idx 2: necessary (p = right, S = {{1}})
theorem w4_5 : ¬ drop0% LGame.IsStrategy.sUnion 2 := fun h => by
  have := @h Player.right {{1}}
  obtain ⟨r, hr, -⟩ := this 1 (by simp) 0 (by simp)
  simp at hr
-- `LGame.IsStrategy.not_isWin'` idx 3: necessary (p = left, s = {on})
theorem w4_6 : ¬ drop0% LGame.IsStrategy.not_isWin' 3 := fun h =>
  @h Player.left LGame.on {LGame.on} rfl W1c4.on_win
-- `LGame.IsStrategy.not_isWin'` idx 4: necessary (s = ∅, x = on)
theorem w4_7 : ¬ drop0% LGame.IsStrategy.not_isWin' 4 := fun h =>
  @h Player.left LGame.on ∅ (fun _ hy => hy.elim) W1c4.on_win
-- `LGame.IsStrategy.not_isWin` idx 3: necessary (p = right, s = {on})
theorem w4_8 : ¬ drop0% LGame.IsStrategy.not_isWin 3 := fun h =>
  @h Player.right LGame.on {LGame.on} rfl W1c4.on_win
-- `LGame.IsStrategy.not_isWin` idx 4: necessary (s = ∅, x = on)
theorem w4_9 : ¬ drop0% LGame.IsStrategy.not_isWin 4 := fun h =>
  @h Player.right LGame.on ∅ (fun _ hy => hy.elim) W1c4.on_win
-- `LGame.not_isLoss_of_isWin` idx 2: necessary (x = 0)
theorem w4_10 : ¬ drop0% LGame.not_isLoss_of_isWin 2 := fun h =>
  @h Player.left 0 (W1c4.zero_loss _)
-- `LGame.not_isWin_of_isLoss` idx 2: necessary (x = on)
theorem w4_11 : ¬ drop0% LGame.not_isWin_of_isLoss 2 := fun h =>
  @h Player.left LGame.on W1c4.on_win
-- `LGame.IsWin.neg` idx 2: necessary (x = 0)
theorem w4_12 : ¬ drop0% LGame.IsWin.neg 2 := fun h =>
  W1c4.zero_not_win _ (by simpa using @h Player.left 0)
-- `LGame.IsLoss.neg` idx 2: necessary (x = on)
theorem w4_13 : ¬ drop0% LGame.IsLoss.neg 2 := fun h =>
  LGame.not_isLoss_of_isWin W1c4.on_win.{0} (by simpa using @h Player.left LGame.on)
-- `LGame.IsDraw.not_isWin` idx 2: necessary (x = on)
theorem w4_14 : ¬ drop0% LGame.IsDraw.not_isWin 2 := fun h =>
  @h Player.left LGame.on W1c4.on_win
-- `LGame.IsDraw.not_isLoss` idx 2: necessary (x = 0)
theorem w4_15 : ¬ drop0% LGame.IsDraw.not_isLoss 2 := fun h =>
  @h Player.left 0 (W1c4.zero_loss _)
-- `LGame.IsDraw.neg` idx 2: necessary (x = 0)
theorem w4_16 : ¬ drop0% LGame.IsDraw.neg 2 := fun h =>
  (by simpa using @h Player.right 0 : LGame.IsDraw Player.left 0).not_isLoss (W1c4.zero_loss _)
-- `LGame.StopperFor.not_isDraw` idx 2: necessary (x = dud)
theorem w4_17 : ¬ drop0% LGame.StopperFor.not_isDraw 2 := fun h =>
  @h Player.left LGame.dud (LGame.isDraw_dud _)
-- `LGame.Stopper.not_isDraw` idx 2: necessary (x = dud)
theorem w4_18 : ¬ drop0% LGame.Stopper.not_isDraw 2 := fun h =>
  @h LGame.dud Player.left (LGame.isDraw_dud _)

namespace W1c4
theorem sta_one : ((priv% _private.CombinatorialGames.Game.Loopy.StoppingTime.«0».LGame.stoppingTimeApprox) Player.left).lfp (1 : LGame.{0}) = 0 := by
  have h := congrFun (OrderHom.isFixedPt_lfp ((priv% _private.CombinatorialGames.Game.Loopy.StoppingTime.«0».LGame.stoppingTimeApprox) Player.left)) 1
  rw [← h]
  show (⨅ y ∈ LGame.moves Player.left 1, ⨆ i ∈ LGame.moves (-Player.left) y,
    (OrderHom.lfp ((priv% _private.CombinatorialGames.Game.Loopy.StoppingTime.«0».LGame.stoppingTimeApprox) Player.left)) i + 1) = 0
  simp
theorem sta_zero : ((priv% _private.CombinatorialGames.Game.Loopy.StoppingTime.«0».LGame.stoppingTimeApprox) Player.left).lfp (0 : LGame.{0}) = ⊤ := by
  have h := congrFun (OrderHom.isFixedPt_lfp ((priv% _private.CombinatorialGames.Game.Loopy.StoppingTime.«0».LGame.stoppingTimeApprox) Player.left)) 0
  rw [← h]
  show (⨅ y ∈ LGame.moves Player.left 0, ⨆ i ∈ LGame.moves (-Player.left) y,
    (OrderHom.lfp ((priv% _private.CombinatorialGames.Game.Loopy.StoppingTime.«0».LGame.stoppingTimeApprox) Player.left)) i + 1) = ⊤
  simp
end W1c4

-- `_private.CombinatorialGames.Game.Loopy.StoppingTime.0.LGame.le_of_finite` idx 3: necessary (x = ⊤ constant, y = lfp, i = 1)
theorem w4_19 : ¬ drop0% _private.CombinatorialGames.Game.Loopy.StoppingTime.«0».LGame.le_of_finite 3 := fun h => by
  have := @h Player.left (fun _ => ⊤) _ (OrderHom.isFixedPt_lfp _) 1 (by rw [W1c4.sta_one]; simp)
  rw [W1c4.sta_one] at this
  simp at this
-- `_private.CombinatorialGames.Game.Loopy.StoppingTime.0.LGame.le_of_finite` idx 4: necessary (x = lfp, y = 0 constant, i = 0)
theorem w4_20 : ¬ drop0% _private.CombinatorialGames.Game.Loopy.StoppingTime.«0».LGame.le_of_finite 4 := fun h => by
  have := @h Player.left _ (fun _ => 0) (OrderHom.isFixedPt_lfp _) 0 (by simp)
  rw [W1c4.sta_zero] at this
  simp at this
-- `LGame.stoppingTime_of_eq` idx 2: necessary (p = left, q = right, x = 0)
theorem w4_21 : ¬ drop0% LGame.stoppingTime_of_eq 2 := fun h => by
  have := @h Player.left Player.right 0
  rw [LGame.stoppingTime_of_ne (by decide)] at this
  simp at this
-- `LGame.stoppingTime_of_ne` idx 2: necessary (p = q = left, x = 0)
theorem w4_22 : ¬ drop0% LGame.stoppingTime_of_ne 2 := fun h => by
  have := @h Player.left Player.left 0
  rw [LGame.stoppingTime_of_eq rfl] at this
  simp at this
-- `LGame.stoppingTime_induction` idx 3: necessary (val left = ⊤, val right = 0, x = off)
theorem w4_23 : ¬ drop0% LGame.stoppingTime_induction 3 := fun h => by
  have := h Player.left (fun q _ => if q = Player.left then ⊤ else 0) (fun x => by simp) Player.right LGame.off
  rw [LGame.stoppingTime_of_ne (by decide)] at this
  have h2 := (le_iSup₂ (f := fun y (_ : y ∈ LGame.off.moves Player.right) =>
    LGame.stoppingTime Player.left (-Player.right) y + 1) LGame.off (by simp)).trans this
  simp only [ite_eq_right (by decide : Player.right ≠ Player.left)] at h2
  revert h2
  generalize LGame.stoppingTime _ _ _ = a
  induction a using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    intro h2
    have : ((n + 1 : NatOrdinal) : WithTop NatOrdinal) ≤ 0 := by simpa using h2
    rw [WithTop.coe_le_zero] at this
    simp at this
-- `LGame.stoppingTime_coinduction` idx 2: necessary (val left = ⊤, val right = 0, x = 1)
theorem w4_24 : ¬ drop0% LGame.stoppingTime_coinduction 2 := fun h => by
  have := h Player.left (fun q _ => if q = Player.left then ⊤ else 0) (fun x => by simp) Player.left 1
  rw [LGame.stoppingTime_of_eq rfl] at this
  simp [LGame.stoppingTime_of_ne] at this
-- `LGame.stoppingTime_coinduction` idx 3: necessary (val left = 0, val right = ⊤, x = 0)
theorem w4_25 : ¬ drop0% LGame.stoppingTime_coinduction 3 := fun h => by
  have := h Player.left (fun q _ => if q = Player.left then 0 else ⊤) (fun x => by simp) Player.right 0
  rw [LGame.stoppingTime_of_ne (by decide)] at this
  simp at this

namespace W1c4
theorem notSmallIGame.{u} : ¬ Small.{u} (Set.univ : Set IGame.{u}) := by
  rw [small_univ_iff]; intro h
  exact not_small_ordinal.{u} (small_of_injective (f := fun o : NatOrdinal.{u} => NatOrdinal.toIGame o)
    NatOrdinal.toIGame.injective)
theorem miny0_neg : IGame.miny 0 < 0 := by game_cmp
end W1c4

-- `IGame.tiny_lf_of_not_nonpos_of_forall_neg_le` idx 3: necessary (x = tiny 0, a = 0)
theorem w4_26 : ¬ drop0% IGame.tiny_lf_of_not_nonpos_of_forall_neg_le 3 := fun h =>
  (@h (IGame.tiny 0) 0 (IGame.tiny_pos 0).not_ge) le_rfl
-- `IGame.tiny_le_of_pos_of_forall_neg_le` idx 3: necessary (x = tiny 0, a = -1)
theorem w4_27 : ¬ drop0% IGame.tiny_le_of_pos_of_forall_neg_le 3 := fun h =>
  absurd (@h (IGame.tiny 0) (-1) (IGame.tiny_pos 0)) (by game_cmp)
-- `IGame.lf_miny_of_not_nonneg_of_forall_le` idx 3: necessary (x = miny 0, a = 0)
theorem w4_28 : ¬ drop0% IGame.lf_miny_of_not_nonneg_of_forall_le 3 := fun h =>
  (@h (IGame.miny 0) 0 W1c4.miny0_neg.not_ge) le_rfl
-- `IGame.le_miny_of_neg_of_forall_le_neg` idx 3: necessary (x = miny 0, a = -1)
theorem w4_29 : ¬ drop0% IGame.le_miny_of_neg_of_forall_le_neg 3 := fun h =>
  absurd (@h (IGame.miny 0) (-1) W1c4.miny0_neg) (by game_cmp)
-- `IGame.tiny_lt_of_toIGame_birthday_le` idx 3: necessary (x = tiny 0, o = 0)
theorem w4_30 : ¬ drop0% IGame.tiny_lt_of_toIGame_birthday_le 3 := fun h =>
  lt_irrefl _ (@h (IGame.tiny 0) (IGame.tiny_pos 0) 0)
-- `IGame.fuzzy_tiny_of_birthday_le` idx 3: necessary (x = star, o = -1)
theorem w4_31 : ¬ drop0% IGame.fuzzy_tiny_of_birthday_le 3 := fun h =>
  (@h IGame.star (by game_cmp) (-1)).1 (by game_cmp)
-- `IGame.lt_miny_toIGame_of_birthday_le` idx 3: necessary (x = miny 0, o = 0)
theorem w4_32 : ¬ drop0% IGame.lt_miny_toIGame_of_birthday_le 3 := fun h =>
  lt_irrefl (IGame.miny.{0} 0) (by simpa using @h (IGame.miny 0) W1c4.miny0_neg 0)
-- `IGame.fuzzy_miny_of_birthday_le` idx 3: necessary (x = star, o = -1)
theorem w4_33 : ¬ drop0% IGame.fuzzy_miny_of_birthday_le 3 := fun h =>
  (@h IGame.star (by game_cmp) (-1)).2 (by game_cmp)
-- `NatOrdinal.forall_mem_moves_left_toIGame_ofNat` idx 2: necessary (n = 0)
theorem w4_34 : ¬ indep0% NatOrdinal.forall_mem_moves_left_toIGame_ofNat 2 := fun h =>
  absurd (@h (fun _ => True) 0).prop (by decide)
-- `NatOrdinal.exists_moves_left_toIGame_ofNat` idx 2: necessary (n = 0)
theorem w4_35 : ¬ indep0% NatOrdinal.exists_moves_left_toIGame_ofNat 2 := fun h =>
  absurd (@h (fun _ => True) 0).prop (by decide)
-- `IGame.Short.exists_neg_natCast_lt` idx 1: necessary (x = -ω)
theorem w4_36 : ¬ drop0% IGame.Short.exists_neg_natCast_lt 1 := fun h => by
  obtain ⟨n, hn⟩ := h (-NatOrdinal.toIGame (NatOrdinal.of Ordinal.omega0))
  rw [IGame.neg_lt_neg_iff] at hn
  exact (IGame.Short.lt_omega0 (n : IGame)).asymm hn
-- `IGame.Short.neg_omega0_lt` idx 1: necessary (x = -ω)
theorem w4_37 : ¬ drop0% IGame.Short.neg_omega0_lt 1 := fun h =>
  lt_irrefl _ (h (-NatOrdinal.toIGame (NatOrdinal.of Ordinal.omega0)))
-- `IGame.ordinalSum_fuzzy_iff_of_forall_wsubposition` idx 3: necessary (x = z = 0, y = star)
theorem w4_38 : ¬ drop0% IGame.ordinalSum_fuzzy_iff_of_forall_wsubposition 3 := fun h => by
  have := @h 0 IGame.star 0
  rw [IGame.zero_ordinalSum] at this
  exact absurd (this.1 (by game_cmp)) (by game_cmp)
-- `IGame.fuzzy_ordinalSum_iff_of_forall_wsubposition` idx 3: necessary (x = z = 0, y = star)
theorem w4_39 : ¬ drop0% IGame.fuzzy_ordinalSum_iff_of_forall_wsubposition 3 := fun h => by
  have := @h 0 IGame.star 0
  rw [IGame.zero_ordinalSum] at this
  exact absurd (this.1 (by game_cmp)) (by game_cmp)
-- `Player.const_of_left_eq_right'` idx 1: necessary (f = (· = left))
theorem w4_40 : ¬ drop0% Player.const_of_left_eq_right' 1 := fun h =>
  absurd ((@h (· = Player.left) Player.left Player.right).1 rfl) (by decide)
-- `ofSets_eq_ofSets_cases` idx 4: necessary (Valid = False)
theorem w4_41 : ¬ indep0% ofSets_eq_ofSets_cases 4 := fun h =>
  @h PUnit.{2} (fun _ => False) ⟨fun _ h _ _ => h.elim⟩ (fun _ => ∅) small_empty small_empty
-- `ofSets_eq_ofSets_cases` idx 5: necessary (IGame, left set univ)
theorem w4_42 : ¬ indep0% ofSets_eq_ofSets_cases 5 := fun h =>
  W1c4.notSmallIGame (@h IGame _ _ (Player.cases Set.univ ∅) trivial (small_empty (α := IGame.{0})))
-- `ofSets_eq_ofSets_cases` idx 6: necessary (IGame, right set univ)
theorem w4_43 : ¬ indep0% ofSets_eq_ofSets_cases 6 := fun h =>
  W1c4.notSmallIGame (@h IGame _ _ (Player.cases ∅ Set.univ) trivial (small_empty (α := IGame.{0})))

namespace W1c4
theorem notSmall_of_le (x y : IGame) [IGame.Numeric y] (hy : 0 < y) (h : ¬ x ≤ y) : ¬ IGame.Small x :=
  fun _ => h (IGame.Small.le_numeric_of_pos x hy)
theorem notSmall_of_ge (x y : IGame) [IGame.Numeric y] (hy : y < 0) (h : ¬ y ≤ x) : ¬ IGame.Small x :=
  fun _ => h (IGame.Small.numeric_le_of_neg x hy)
theorem notSmall_of_lt (x y : IGame) [IGame.Numeric y] (hy : 0 < y) (h : ¬ x < y) : ¬ IGame.Small x :=
  fun _ => h (IGame.Small.lt_numeric_of_pos x hy)
theorem notSmall_of_gt (x y : IGame) [IGame.Numeric y] (hy : y < 0) (h : ¬ y < x) : ¬ IGame.Small x :=
  fun _ => h (IGame.Small.numeric_lt_of_neg x hy)
theorem notSmallOne : ¬ IGame.Small 1 := notSmall_of_lt 1 1 (by game_cmp) (by game_cmp)
theorem notSmallTwo : ¬ IGame.Small 2 := notSmall_of_le 2 1 (by game_cmp) (by game_cmp)
theorem notSmallNegOne : ¬ IGame.Small (-1) := notSmall_of_gt (-1) (-1) (by game_cmp) (by game_cmp)
theorem notSmallTinyNegTwo : ¬ IGame.Small (IGame.tiny (-2)) :=
  notSmall_of_lt _ IGame.half (by game_cmp) (by game_cmp)
theorem notSmallMinyNegTwo : ¬ IGame.Small (IGame.miny (-2)) :=
  notSmall_of_gt _ (-IGame.half) (by game_cmp) (by game_cmp)
theorem notSmallSwitchOne : ¬ IGame.Small (IGame.switch 1) := notSmall_of_le _ 1 (by game_cmp) (by game_cmp)
instance short10 : IGame.Short !{{1} | {0}} := by rw [IGame.short_def]; simp
theorem notSmall10 : ¬ IGame.Small !{{1} | {0}} := notSmall_of_le _ 1 (by game_cmp) (by game_cmp)
theorem rightStop10 : IGame.rightStop !{{1} | {0}} = 0 := by
  have h := IGame.toSurreal_rightGame_mk_of_short !{{1} | {0}}
  have e : Surreal.Cut.rightGame (Game.mk !{{1} | {0}}) = Surreal.Cut.leftSurreal 0 := by
    rw [Surreal.Cut.rightGame_eq_infRight_of_le (by
      simp only [Surreal.Cut.infRight, Surreal.Cut.supLeft]
      simp
      exact (Surreal.Cut.leftSurreal_lt_rightSurreal_iff.2 zero_le_one).le)]
    simp [Surreal.Cut.infRight]
  rw! [e] at h
  simp at h
  exact_mod_cast h.symm
end W1c4

-- `IGame.Small.le_numeric_of_pos` idx 3: necessary (x = star, y = up)
theorem w4_44 : ¬ drop0% IGame.Small.le_numeric_of_pos 3 := fun h =>
  absurd (@h IGame.star inferInstance IGame.up (by game_cmp)) (by game_cmp)
-- `IGame.Small.numeric_le_of_neg` idx 1: necessary (x = -2, y = -1)
theorem w4_45 : ¬ drop0% IGame.Small.numeric_le_of_neg 1 := fun h =>
  absurd (@h (-2) (-1) inferInstance (by game_cmp)) (by game_cmp)
-- `IGame.Small.numeric_le_of_neg` idx 3: necessary (x = star, y = down)
theorem w4_46 : ¬ drop0% IGame.Small.numeric_le_of_neg 3 := fun h =>
  absurd (@h IGame.star inferInstance IGame.down (by game_cmp)) (by game_cmp)
-- `IGame.Small.lt_numeric_of_pos` idx 3: necessary (x = star, y = up)
theorem w4_47 : ¬ drop0% IGame.Small.lt_numeric_of_pos 3 := fun h =>
  absurd (@h IGame.star IGame.up inferInstance (by game_cmp)) (by game_cmp)
-- `IGame.Small.numeric_lt_of_neg` idx 2: necessary (x = -2, y = -1)
theorem w4_48 : ¬ drop0% IGame.Small.numeric_lt_of_neg 2 := fun h =>
  absurd (@h (-2) (-1) inferInstance (by game_cmp)) (by game_cmp)
-- `IGame.Small.numeric_lt_of_neg` idx 3: necessary (x = star, y = down)
theorem w4_49 : ¬ drop0% IGame.Small.numeric_lt_of_neg 3 := fun h =>
  absurd (@h IGame.star IGame.down inferInstance (by game_cmp)) (by game_cmp)
-- `IGame.Small.surreal_lt_of_neg` idx 1: necessary (x = -1, y = -1)
theorem w4_50 : ¬ drop0% IGame.Small.surreal_lt_of_neg 1 := fun h => by
  have := @h (-1) (-1) (by simp)
  simp at this
-- `IGame.Small.of_equiv` idx 3: necessary (x = y = 1)
theorem w4_51 : ¬ drop0% IGame.Small.of_equiv 3 := fun h =>
  W1c4.notSmallOne (@h 1 1 AntisymmRel.rfl)
-- `IGame.Small.congr` idx 2: necessary (x = 0, y = 1)
theorem w4_52 : ¬ drop0% IGame.Small.congr 2 := fun h =>
  W1c4.notSmallOne ((@h 0 1).1 IGame.Small.zero)
-- `IGame.Numeric.small_iff_equiv_zero` idx 1: necessary (x = star)
theorem w4_53 : ¬ drop0% IGame.Numeric.small_iff_equiv_zero 1 := fun h =>
  absurd ((@h IGame.star).1 inferInstance) (by game_cmp)
-- `IGame.Small.add` idx 3: necessary (x = 0, y = 1)
theorem w4_54 : ¬ drop0% IGame.Small.add 3 := fun h =>
  W1c4.notSmallOne (by simpa using @h 0 1 IGame.Small.zero)
-- `IGame.Small.of_between` idx 3: necessary (x = z = -1, y = 0)
theorem w4_55 : ¬ drop0% IGame.Small.of_between 3 := fun h =>
  W1c4.notSmallNegOne (@h (-1) 0 (-1) IGame.Small.zero ⟨le_rfl, by game_cmp⟩)
-- `IGame.Small.of_between` idx 4: necessary (x = 0, y = z = 1)
theorem w4_56 : ¬ drop0% IGame.Small.of_between 4 := fun h =>
  W1c4.notSmallOne (@h 0 1 1 IGame.Small.zero ⟨by game_cmp, le_rfl⟩)
-- `IGame.Small.of_between` idx 5: necessary (x = y = 0, z = 1)
theorem w4_57 : ¬ drop0% IGame.Small.of_between 5 := fun h =>
  W1c4.notSmallOne (@h 0 0 1 IGame.Small.zero IGame.Small.zero)
-- `IGame.Small.leftGame_mk_cases` idx 1: necessary (x = 1)
theorem w4_58 : ¬ drop0% IGame.Small.leftGame_mk_cases 1 := fun h => by
  have := h 1
  simp [Surreal.Cut.leftGame_one, Surreal.Cut.leftSurreal_ne_rightSurreal] at this
-- `IGame.Small.rightGame_mk_cases` idx 1: necessary (x = 1)
theorem w4_59 : ¬ drop0% IGame.Small.rightGame_mk_cases 1 := fun h => by
  have := h 1
  simp [Surreal.Cut.rightGame_one, Surreal.Cut.leftSurreal_ne_rightSurreal] at this
-- `IGame.Small.toSurreal_leftGame_mk` idx 1: necessary (x = 1)
theorem w4_60 : ¬ indep0% IGame.Small.toSurreal_leftGame_mk 1 := fun h => W1c4.notSmallOne (h 1)
-- `IGame.Small.toSurreal_rightGame_mk` idx 1: necessary (x = 1)
theorem w4_61 : ¬ indep0% IGame.Small.toSurreal_rightGame_mk 1 := fun h => W1c4.notSmallOne (h 1)
-- `IGame.Small.of_stops_eq_zero` idx 2: necessary (x = !{{1} | {0}})
theorem w4_62 : ¬ drop0% IGame.Small.of_stops_eq_zero 2 := fun h =>
  W1c4.notSmall10 (@h _ inferInstance W1c4.rightStop10)
-- `IGame.Small.of_stops_eq_zero` idx 3: necessary (x = -!{{1} | {0}})
theorem w4_63 : ¬ drop0% IGame.Small.of_stops_eq_zero 3 := fun h =>
  W1c4.notSmall10 (IGame.Small.neg_iff.1 (@h (-!{{1} | {0}}) inferInstance (by rw [IGame.leftStop_neg, W1c4.rightStop10, neg_zero])))
-- `IGame.Small.confusionInterval_subset_zero` idx 1: necessary (x = ±1, interval [-1, 1])
theorem w4_64 : ¬ drop0% IGame.Small.confusionInterval_subset_zero 1 := fun h => by
  have := h (IGame.switch 1)
  rw [Game.confusionInterval_switch_of_numeric (by game_cmp)] at this
  have h1 := this (show (1 : Surreal) ∈ Set.Icc (-Surreal.mk 1) (Surreal.mk 1) by simp)
  simp at h1
-- `IGame.Small.lt_numeric_of_pos_of_forall_of_nonempty` idx 3: necessary (x = star, y = up)
theorem w4_65 : ¬ drop0% IGame.Small.lt_numeric_of_pos_of_forall_of_nonempty 3 := fun h =>
  absurd (@h IGame.star IGame.up (by game_cmp) (by simp) (by simp)) (by game_cmp)
-- `IGame.Small.lt_numeric_of_pos_of_forall_of_nonempty` idx 4: necessary (x = !{{1} | {2}}, y = 1)
theorem w4_66 : ¬ drop0% IGame.Small.lt_numeric_of_pos_of_forall_of_nonempty 4 := fun h =>
  absurd (@h !{{1} | {2}} 1 (by game_cmp) inferInstance (by simp)) (by game_cmp)
-- `IGame.Small.numeric_lt_of_neg_of_forall_of_nonempty` idx 3: necessary (x = star, y = down)
theorem w4_67 : ¬ drop0% IGame.Small.numeric_lt_of_neg_of_forall_of_nonempty 3 := fun h =>
  absurd (@h IGame.star IGame.down (by game_cmp) (by simp) (by simp)) (by game_cmp)
-- `IGame.Small.numeric_lt_of_neg_of_forall_of_nonempty` idx 4: necessary (x = !{{-2} | {-1}}, y = -1)
theorem w4_68 : ¬ drop0% IGame.Small.numeric_lt_of_neg_of_forall_of_nonempty 4 := fun h =>
  absurd (@h !{{-2} | {-1}} (-1) (by game_cmp) inferInstance (by simp)) (by game_cmp)
-- `IGame.Small.numeric_lt_of_neg_of_forall_of_nonempty` idx 5: necessary (x = !{∅ | {0}}, y = -1)
theorem w4_69 : ¬ drop0% IGame.Small.numeric_lt_of_neg_of_forall_of_nonempty 5 := fun h =>
  absurd (@h !{∅ | {0}} (-1) (by game_cmp) inferInstance (by simp)) (by game_cmp)
-- `IGame.Small.of_forall_of_nonempty` idx 1: necessary (x = !{{1} | {1}})
theorem w4_70 : ¬ drop0% IGame.Small.of_forall_of_nonempty 1 := fun h =>
  W1c4.notSmall_of_le !{{1} | {1}} 1 (by game_cmp) (by game_cmp) (@h _ (by simp))
-- `IGame.Small.of_forall_of_nonempty` idx 2: necessary (x = 1)
theorem w4_71 : ¬ drop0% IGame.Small.of_forall_of_nonempty 2 := fun h =>
  W1c4.notSmallOne (@h 1 (by simp))
-- `IGame.Dicotic.toSmall` idx 1: necessary (x = 1)
theorem w4_72 : ¬ drop0% IGame.Dicotic.toSmall 1 := fun h => W1c4.notSmallOne (h 1)
-- `IGame.Impartial.toSmall` idx 1: necessary (x = 1)
theorem w4_73 : ¬ drop0% IGame.Impartial.toSmall 1 := fun h => W1c4.notSmallOne (h 1)
-- `IGame.Small.ofSets_zero_left` idx 1: necessary (x = 2)
theorem w4_74 : ¬ drop0% IGame.Small.ofSets_zero_left 1 := fun h =>
  W1c4.notSmall_of_le !{{0} | {2}} IGame.half (by game_cmp) (by game_cmp) (h 2)
-- `IGame.Small.ofSets_zero_right` idx 1: necessary (x = -2)
theorem w4_75 : ¬ drop0% IGame.Small.ofSets_zero_right 1 := fun h =>
  W1c4.notSmall_of_ge !{{-2} | {0}} (-IGame.half) (by game_cmp) (by game_cmp) (h (-2))
-- `IGame.Small.tiny` idx 1: necessary (x = -2)
theorem w4_76 : ¬ drop0% IGame.Small.tiny 1 := fun h => W1c4.notSmallTinyNegTwo (h (-2))
-- `IGame.Small.miny` idx 1: necessary (x = -2)
theorem w4_77 : ¬ drop0% IGame.Small.miny 1 := fun h => W1c4.notSmallMinyNegTwo (h (-2))
-- `IGame.Small.tiny_of_nonneg` idx 1: necessary (x = -2)
theorem w4_78 : ¬ drop0% IGame.Small.tiny_of_nonneg 1 := fun h => W1c4.notSmallTinyNegTwo (@h (-2))
-- `IGame.Small.miny_of_nonneg` idx 1: necessary (x = -2)
theorem w4_79 : ¬ drop0% IGame.Small.miny_of_nonneg 1 := fun h => W1c4.notSmallMinyNegTwo (@h (-2))
-- `IGame.instDicoticTiny` idx 1: necessary (x = -2, tiny not small)
theorem w4_80 : ¬ drop0% IGame.instDicoticTiny 1 := fun h =>
  W1c4.notSmallTinyNegTwo (@IGame.Dicotic.toSmall _ (h (-2)))
-- `IGame.instDicoticMiny` idx 1: necessary (x = -2, miny not small)
theorem w4_81 : ¬ drop0% IGame.instDicoticMiny 1 := fun h =>
  W1c4.notSmallMinyNegTwo (@IGame.Dicotic.toSmall _ (h (-2)))
-- `IGame.instDicoticSwitch` idx 1: necessary (x = 1, switch not small)
theorem w4_82 : ¬ drop0% IGame.instDicoticSwitch 1 := fun h =>
  W1c4.notSmallSwitchOne (@IGame.Dicotic.toSmall _ (h 1))
-- `IGame.tiny_congr` idx 2: necessary (x = -1, y = -2)
theorem w4_83 : ¬ drop0% IGame.tiny_congr 2 := fun h =>
  absurd (@h (-1) (-2)) (by game_cmp)

namespace W1c4
local notation "ωI" => NatOrdinal.toIGame (NatOrdinal.of Ordinal.omega0)
theorem notShortOmega : ¬ IGame.Short ωI := fun _ => lt_irrefl _ (IGame.Short.lt_omega0 ωI)
theorem omegaPos : (0 : IGame) < ωI := by
  rw [← NatOrdinal.toIGame_zero, NatOrdinal.toIGame.lt_iff_lt]
  exact Ordinal.omega0_pos
/-- a non-short game equivalent to 0 -/
theorem zw_equiv : !{∅ | {ωI}} ≈ 0 := by
  constructor
  · show _ ≤ _
    rw [IGame.le_iff_forall_lf]; simp
  · show _ ≤ _
    rw [IGame.le_iff_forall_lf]
    simp only [IGame.moves_left_ofSets, IGame.moves_right_ofSets]
    refine ⟨by simp, ?_⟩
    simp only [Set.mem_singleton_iff, forall_eq]
    exact omegaPos.not_ge
theorem notShortZW : ¬ IGame.Short !{∅ | {ωI}} := fun _ =>
  notShortOmega (IGame.Short.of_mem_moves (x := !{∅ | {ωI}}) (p := Player.right) (by simp))
theorem notShortTinyOmega : ¬ IGame.Short (IGame.tiny ωI) := fun h => notShortOmega (IGame.short_tiny_iff.1 h)
theorem smallTinyOmega : IGame.Small (IGame.tiny ωI) := IGame.Small.tiny_of_nonneg omegaPos.le
end W1c4

local notation "ωI" => NatOrdinal.toIGame (NatOrdinal.of Ordinal.omega0)
-- `IGame.leftStop_of_small` idx 2: necessary (x = tiny ω: small, not short)
theorem w4_84 : ¬ indep0% IGame.leftStop_of_small 2 := fun h =>
  W1c4.notShortTinyOmega (@h _ W1c4.smallTinyOmega)
-- `IGame.rightStop_of_small` idx 2: necessary (x = tiny ω: small, not short)
theorem w4_85 : ¬ indep0% IGame.rightStop_of_small 2 := fun h =>
  W1c4.notShortTinyOmega (@h _ W1c4.smallTinyOmega)
-- `IGame.Small.of_stops_eq_zero` idx 1: necessary (x = ω)
theorem w4_86 : ¬ indep0% IGame.Small.of_stops_eq_zero 1 := fun h => W1c4.notShortOmega (@h ωI)
-- `IGame.Small.of_infinitesimal` idx 3: necessary (x = 1)
theorem w4_87 : ¬ drop0% IGame.Small.of_infinitesimal 3 := fun h =>
  W1c4.notSmallOne (@h 1 inferInstance fun y hy => (Dyadic.toIGame_le_zero.2 hy.le).trans zero_le_one)
-- `IGame.instShortTiny` idx 1: necessary (x = ω)
theorem w4_88 : ¬ drop0% IGame.instShortTiny 1 := fun h => W1c4.notShortTinyOmega (h ωI)
-- `IGame.instShortMiny` idx 1: necessary (x = ω)
theorem w4_89 : ¬ drop0% IGame.instShortMiny 1 := fun h =>
  W1c4.notShortOmega (IGame.short_miny_iff.1 (h ωI))
-- `IGame.instShortSwitch` idx 1: necessary (x = ω)
theorem w4_90 : ¬ drop0% IGame.instShortSwitch 1 := fun h =>
  W1c4.notShortOmega (IGame.short_switch_iff.1 (h ωI))
-- `_private.CombinatorialGames.Game.Stops.0.IGame.stop_aux₁` idx 1: necessary (x = ⊤, birthday 0)
theorem w4_91 : ¬ indep0% _private.CombinatorialGames.Game.Stops.«0».IGame.stop_aux₁ 1 := fun h =>
  Surreal.Cut.Numeric.ne_top ⊤ (hx := @h ⊤ (by simp [Surreal.Cut.birthday_top])) rfl
-- `_private.CombinatorialGames.Game.Stops.0.IGame.stop_aux₁` idx 2: necessary (x = leftSurreal ω)
theorem w4_92 : ¬ drop0% _private.CombinatorialGames.Game.Stops.«0».IGame.stop_aux₁ 2 := fun h => by
  have := @h (Surreal.Cut.leftSurreal (NatOrdinal.of Ordinal.omega0).toSurreal) inferInstance
  rw [Surreal.Cut.toSurreal_leftSurreal, ← Surreal.birthday_lt_omega0_iff, Surreal.birthday_toSurreal] at this
  exact lt_irrefl _ this
-- `_private.CombinatorialGames.Game.Stops.0.IGame.stop_aux₂` idx 1: necessary (x = ω)
theorem w4_93 : ¬ drop0% _private.CombinatorialGames.Game.Stops.«0».IGame.stop_aux₂ 1 := fun h => by
  have := h ωI
  rw [Game.mk_natOrdinal_toIGame, Game.birthday_toGame] at this
  exact (lt_irrefl _ ((WithTop.coe_le_coe.2 le_rfl).trans_lt ((le_add_of_nonneg_right zero_le_one).trans_lt this)))
-- `IGame.toSurreal_leftGame_mk_of_short` idx 1: necessary (x = ω)
theorem w4_94 : ¬ indep0% IGame.toSurreal_leftGame_mk_of_short 1 := fun h => W1c4.notShortOmega (h ωI)
-- `IGame.toSurreal_rightGame_mk_of_short` idx 1: necessary (x = ω)
theorem w4_95 : ¬ indep0% IGame.toSurreal_rightGame_mk_of_short 1 := fun h => W1c4.notShortOmega (h ωI)
-- `IGame.leftStop_of_numeric` idx 1: necessary (x = ω)
theorem w4_96 : ¬ indep0% IGame.leftStop_of_numeric 1 := fun h => W1c4.notShortOmega (h ωI)
-- `IGame.rightStop_of_numeric` idx 1: necessary (x = ω)
theorem w4_97 : ¬ indep0% IGame.rightStop_of_numeric 1 := fun h => W1c4.notShortOmega (h ωI)
-- `IGame.lt_of_leftStop_lt` idx 2: necessary (x = ω)
theorem w4_98 : ¬ indep0% IGame.lt_of_leftStop_lt 2 := fun h => W1c4.notShortOmega (@h ωI 0 inferInstance)
-- `IGame.lt_of_leftStop_lt` idx 3: necessary (x = star, y = up)
theorem w4_99 : ¬ drop0% IGame.lt_of_leftStop_lt 3 := fun h =>
  absurd (@h IGame.star IGame.up inferInstance (by simp)) (by game_cmp)
-- `IGame.lf_of_lt_leftStop` idx 2: necessary (x = ω)
theorem w4_100 : ¬ indep0% IGame.lf_of_lt_leftStop 2 := fun h => W1c4.notShortOmega (@h ωI 0 inferInstance)
-- `IGame.lf_of_lt_leftStop` idx 3: necessary (x = y = down)
theorem w4_101 : ¬ drop0% IGame.lf_of_lt_leftStop 3 := fun h =>
  (@h IGame.down IGame.down inferInstance (by simp)) le_rfl
-- `IGame.lt_of_lt_rightStop` idx 2: necessary (x = ω)
theorem w4_102 : ¬ indep0% IGame.lt_of_lt_rightStop 2 := fun h => W1c4.notShortOmega (@h ωI 0 inferInstance)
-- `IGame.lt_of_lt_rightStop` idx 3: necessary (x = star, y = down)
theorem w4_103 : ¬ drop0% IGame.lt_of_lt_rightStop 3 := fun h =>
  absurd (@h IGame.star IGame.down inferInstance (by simp)) (by game_cmp)
-- `IGame.lf_of_rightStop_lt` idx 2: necessary (x = ω)
theorem w4_104 : ¬ indep0% IGame.lf_of_rightStop_lt 2 := fun h => W1c4.notShortOmega (@h ωI 0 inferInstance)
-- `IGame.lf_of_rightStop_lt` idx 3: necessary (x = y = up)
theorem w4_105 : ¬ drop0% IGame.lf_of_rightStop_lt 3 := fun h =>
  (@h IGame.up IGame.up inferInstance (by simp)) le_rfl
-- `IGame.leftStop_neg` idx 1: necessary (x = ω)
theorem w4_106 : ¬ indep0% IGame.leftStop_neg 1 := fun h => W1c4.notShortOmega (h ωI)
-- `IGame.rightStop_neg` idx 1: necessary (x = ω)
theorem w4_107 : ¬ indep0% IGame.rightStop_neg 1 := fun h => W1c4.notShortOmega (h ωI)
-- `IGame.leftStop_congr` idx 2: necessary (x = !{∅ | {ω}}, y = 0)
theorem w4_108 : ¬ indep0% IGame.leftStop_congr 2 := fun h =>
  W1c4.notShortZW (@h _ 0 IGame.Short.zero W1c4.zw_equiv)
-- `IGame.leftStop_congr` idx 3: necessary (x = 0, y = !{∅ | {ω}})
theorem w4_109 : ¬ indep0% IGame.leftStop_congr 3 := fun h =>
  W1c4.notShortZW (@h 0 _ IGame.Short.zero W1c4.zw_equiv.symm)
-- `IGame.rightStop_congr` idx 2: necessary (x = !{∅ | {ω}}, y = 0)
theorem w4_110 : ¬ indep0% IGame.rightStop_congr 2 := fun h =>
  W1c4.notShortZW (@h _ 0 IGame.Short.zero W1c4.zw_equiv)
-- `IGame.rightStop_congr` idx 3: necessary (x = 0, y = !{∅ | {ω}})
theorem w4_111 : ¬ indep0% IGame.rightStop_congr 3 := fun h =>
  W1c4.notShortZW (@h 0 _ IGame.Short.zero W1c4.zw_equiv.symm)
-- `IGame.rightStop_le_leftStop` idx 1: necessary (x = ω)
theorem w4_112 : ¬ indep0% IGame.rightStop_le_leftStop 1 := fun h => W1c4.notShortOmega (h ωI)

namespace W1c4
/-- descending chain of the poset relation on Set ℤ -/
theorem intChain (n : ℕ) : GameGraph.Poset.Rel (Set.Iio (-((n + 1 : ℕ) : ℤ))) (Set.Iio (-(n : ℤ))) :=
  ⟨-(n : ℤ) - 1, by simp, by ext x; simp; omega⟩
theorem notWF_int : ¬ @WellFounded (Set ℤ) GameGraph.Poset.Rel := fun hwf => by
  have key : ∀ s : Set ℤ, ∀ n : ℕ, s ≠ Set.Iio (-(n : ℤ)) := fun s =>
    hwf.induction (C := fun s => ∀ n : ℕ, s ≠ Set.Iio (-(n : ℤ))) s
      (fun s ih n hs => ih _ (hs ▸ intChain n) (n + 1) rfl)
  exact key _ 0 rfl
theorem notWQO_int : ¬ WellQuasiOrderedLE ℤ := fun _ => by
  obtain ⟨m, n, h, h'⟩ := wellQuasiOrdered_le (fun n : ℕ => -(n : ℤ))
  simp at h'; omega
theorem notWQO_natDual : ¬ WellQuasiOrderedLE ℕᵒᵈ := fun _ => by
  obtain ⟨m, n, h, h'⟩ := wellQuasiOrdered_le (fun n : ℕ => OrderDual.toDual n)
  rw [OrderDual.toDual_le_toDual] at h'; omega
end W1c4

-- `IGame.Domineering.subset_of_mem_left` idx 2: necessary (empty board)
theorem w4_113 : ¬ drop0% IGame.Domineering.subset_of_mem_left 2 := fun h => by
  simpa using @h (IGame.toDomineering ∅) (0, 0)
-- `IGame.Domineering.subset_of_mem_right` idx 2: necessary (empty board)
theorem w4_114 : ¬ drop0% IGame.Domineering.subset_of_mem_right 2 := fun h => by
  simpa using @h (IGame.toDomineering ∅) (0, 0)
-- `IGame.Domineering.card_of_mem_left` idx 2: necessary (empty board)
theorem w4_115 : ¬ drop0% IGame.Domineering.card_of_mem_left 2 := fun h => by
  simpa using @h (IGame.toDomineering ∅) (0, 0)
-- `IGame.Domineering.card_of_mem_right` idx 2: necessary (empty board)
theorem w4_116 : ¬ drop0% IGame.Domineering.card_of_mem_right 2 := fun h => by
  simpa using @h (IGame.toDomineering ∅) (0, 0)
-- `IGame.Domineering.moveLeft_card` idx 2: necessary (empty board)
theorem w4_117 : ¬ drop0% IGame.Domineering.moveLeft_card 2 := fun h => by
  simpa [IGame.Domineering.moveLeft] using @h (IGame.toDomineering ∅) (0, 0)
-- `IGame.Domineering.moveRight_card` idx 2: necessary (empty board)
theorem w4_118 : ¬ drop0% IGame.Domineering.moveRight_card 2 := fun h => by
  simpa [IGame.Domineering.moveRight] using @h (IGame.toDomineering ∅) (0, 0)
-- `IGame.Domineering.card_of_relLeft` idx 2: necessary (a = b = empty board)
theorem w4_119 : ¬ drop0% IGame.Domineering.card_of_relLeft 2 := fun h => by
  simpa using @h (IGame.toDomineering ∅) (IGame.toDomineering ∅)
-- `IGame.Domineering.card_of_relRight` idx 2: necessary (a = b = empty board)
theorem w4_120 : ¬ drop0% IGame.Domineering.card_of_relRight 2 := fun h => by
  simpa using @h (IGame.toDomineering ∅) (IGame.toDomineering ∅)
-- `IGame.forall_moves_nim_ofNat` idx 3: necessary (n = 0)
theorem w4_121 : ¬ indep0% IGame.forall_moves_nim_ofNat 3 := fun h =>
  absurd (@h Player.left (fun _ => True) 0).prop (by decide)
-- `IGame.exists_moves_nim_ofNat` idx 3: necessary (n = 0)
theorem w4_122 : ¬ indep0% IGame.exists_moves_nim_ofNat 3 := fun h =>
  absurd (@h Player.left (fun _ => True) 0).prop (by decide)
-- `GameGraph.Poset.rel_univ_of_rel_top_compl` idx 4: necessary (α = Unit, s = univ)
theorem w4_123 : ¬ drop0% GameGraph.Poset.rel_univ_of_rel_top_compl 4 := fun h =>
  GameGraph.Poset.rel_irrefl _ (@h Unit _ _ Set.univ)
-- `GameGraph.Poset.wellFounded_rel` idx 2: necessary (α = ℤ, chain Iio (-n))
theorem w4_124 : ¬ drop0% GameGraph.Poset.wellFounded_rel 2 := fun h => W1c4.notWF_int (@h ℤ _)
-- `GameGraph.Poset.instWellFoundedSetPoset` idx 2: necessary (α = ℤ, chain Iio (-n))
theorem w4_125 : ¬ drop0% GameGraph.Poset.instWellFoundedSetPoset 2 := fun h =>
  W1c4.notWF_int (Subrelation.wf (fun {_ _} hab => ⟨Player.left, hab⟩) (@h ℤ _).wf)
-- `GameGraph.Poset.moves_toIGame` idx 2: necessary (α = ℤ is not a WQO)
theorem w4_126 : ¬ indep0% GameGraph.Poset.moves_toIGame 2 := fun h => W1c4.notWQO_int (@h ℤ _ Player.left ∅)
-- `GameGraph.Poset.mem_moves_toIGame_of_rel` idx 2: necessary (α = ℤ is not a WQO)
theorem w4_127 : ¬ indep0% GameGraph.Poset.mem_moves_toIGame_of_rel 2 := fun h =>
  W1c4.notWQO_int (@h ℤ _ Player.left _ _ (W1c4.intChain 0))
-- `GameGraph.Poset.mem_moves_toIGame_of_rel` idx 6: necessary (α = ℕ, s = t = univ)
theorem w4_128 : ¬ drop0% GameGraph.Poset.mem_moves_toIGame_of_rel 6 := fun h =>
  lt_irrefl _ (IGame.birthday_lt_of_mem_moves (@h ℕ _ _ Player.left Set.univ Set.univ))
-- `GameGraph.Poset.neg_toIGame` idx 2: necessary (α = ℤ is not a WQO)
theorem w4_129 : ¬ indep0% GameGraph.Poset.neg_toIGame 2 := fun h => W1c4.notWQO_int (@h ℤ _ ∅)
-- `GameGraph.Poset.univ_fuzzy_zero` idx 2: necessary (α = ℕᵒᵈ is not a WQO)
theorem w4_130 : ¬ indep0% GameGraph.Poset.univ_fuzzy_zero 2 := fun h => W1c4.notWQO_natDual (@h ℕᵒᵈ _ _)

namespace W1c4
/-- the game with left and right options all natural numbers -/
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
end W1c4

-- `IGame.Small.instNumericCoeOrderHomGameCutLeftGameMk` idx 1: necessary (x = !{ℕ | ℕ}: its left cut is the gap at infinity)
theorem w4_131 : ¬ drop0% IGame.Small.instNumericCoeOrderHomGameCutLeftGameMk 1 := fun h =>
  W1c4.notNumericGap (h W1c4.gapX)
-- `IGame.Small.instNumericCoeOrderHomGameCutRightGameMk` idx 1: necessary (x = -!{ℕ | ℕ}, by negation)
theorem w4_132 : ¬ drop0% IGame.Small.instNumericCoeOrderHomGameCutRightGameMk 1 := fun h => by
  have := h (-W1c4.gapX)
  rw [Game.mk_neg, Surreal.Cut.rightGame_neg] at this
  exact W1c4.notNumericGap (by simpa using (inferInstance : (-(-Surreal.Cut.leftGame (Game.mk W1c4.gapX))).Numeric))

namespace W1c4
/-- a positive numeric infinitesimal: 0 on the left, all positive dyadics on the right -/
noncomputable def epsG : IGame := !{{0} | (fun d : Dyadic => (d : IGame)) '' {d | 0 < d}}
instance numEps : IGame.Numeric epsG := by
  rw [IGame.numeric_def]
  refine ⟨fun y hy z hz => ?_, fun p => ?_⟩
  · simp only [epsG, IGame.moves_left_ofSets, IGame.moves_right_ofSets, Set.mem_singleton_iff,
      Set.mem_image, Set.mem_ofPred_eq] at hy hz
    obtain ⟨d, hd, rfl⟩ := hz
    subst hy
    simpa [← Dyadic.toIGame_zero, Dyadic.toIGame_lt_toIGame] using hd
  · cases p <;> simp [epsG] <;> infer_instance
theorem eps_pos : 0 < epsG := IGame.Numeric.left_lt (by simp [epsG])
end W1c4

-- `IGame.Small.of_infinitesimal` idx 1: necessary (x = !{0 | positive dyadics}, a positive infinitesimal number)
theorem w4_133 : ¬ drop0% IGame.Small.of_infinitesimal 1 := fun h => by
  have hs := @h W1c4.epsG (fun y hy => ((Dyadic.toIGame_le_zero.2 hy.le).trans W1c4.eps_pos.le))
    (fun y hy => (IGame.Numeric.lt_right (by simpa [W1c4.epsG] using hy)).le)
  exact (IGame.Numeric.small_iff_equiv_zero.1 hs).symm.not_lt W1c4.eps_pos
