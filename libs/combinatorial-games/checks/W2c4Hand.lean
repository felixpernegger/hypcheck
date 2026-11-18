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

open Lean Meta Elab Term in
/-- `dropU% T i [l₀, l₁, …]`: `drop% T i` with the universe parameters of `T` set to the given numerals. -/
elab "dropU% " T:ident i:num " [" us:num,* "]" : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := us.getElems.toList.map fun u => Level.ofNat u.getNat
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    mkForallFVars (xs.eraseIdx! i.getNat) body

namespace W2c4
open IGame Set

theorem notSmallUniv : ¬ Small.{0} (Set.univ : Set Surreal.{0}) := by
  intro h
  have h2 : Small.{0} Surreal.{0} := (small_univ_iff).1 h
  have : Small.{0} Ordinal.{0} :=
    small_of_injective (f := fun o : Ordinal.{0} => NatOrdinal.toSurreal (NatOrdinal.of o))
      (fun a b hab => by simpa using hab)
  exact not_small_ordinal.{0, 0} this

theorem notSmallIGame : ¬ Small.{0} (Set.univ : Set IGame.{0}) := by
  rw [small_univ_iff]; intro h
  exact not_small_ordinal.{0} (small_of_injective (f := fun o : NatOrdinal.{0} => NatOrdinal.toIGame o)
    NatOrdinal.toIGame.injective)

theorem smallEmpty : Small.{0} (∅ : Set Surreal.{0}) := @Countable.toSmall _ Set.countable_empty.to_subtype
theorem se : Small.{0} ↑(∅ : Set IGame.{0}) := small_empty
theorem ss (a : Surreal.{0}) : Small.{0} ({a} : Set Surreal.{0}) := small_single a

theorem notNumYS : ¬ Numeric !{{IGame.star} | ∅} := by
  intro hn
  exact not_numeric_star (Numeric.of_mem_moves (p := .left) (x := !{{IGame.star} | ∅}) (by simp))

theorem notSmallIio : ¬ Small.{0} (Set.Iio (0 : Surreal.{0})) := by
  intro h
  have hn : ∀ o : Ordinal.{0}, (0 : Surreal) ≤ NatOrdinal.toSurreal (NatOrdinal.of o) := fun o => by
    rw [← NatOrdinal.toSurreal_zero]
    exact NatOrdinal.toSurreal.monotone _root_.zero_le
  have : Small.{0} Ordinal.{0} := small_of_injective
    (f := fun o : Ordinal.{0} =>
      (⟨-(NatOrdinal.toSurreal (NatOrdinal.of o) + 1), by
        have := hn o; simp only [Set.mem_Iio]; linarith⟩ : Set.Iio (0 : Surreal.{0})))
    (fun a b hab => by
      simp only [Subtype.mk.injEq, neg_inj, add_left_inj] at hab
      simpa using hab)
  exact not_small_ordinal.{0, 0} this

theorem notSmallIoi : ¬ Small.{0} (Set.Ioi (0 : Surreal.{0})) := by
  intro h
  have hn : ∀ o : Ordinal.{0}, (0 : Surreal) ≤ NatOrdinal.toSurreal (NatOrdinal.of o) := fun o => by
    rw [← NatOrdinal.toSurreal_zero]
    exact NatOrdinal.toSurreal.monotone _root_.zero_le
  have : Small.{0} Ordinal.{0} := small_of_injective
    (f := fun o : Ordinal.{0} =>
      (⟨NatOrdinal.toSurreal (NatOrdinal.of o) + 1, by
        have := hn o; simp only [Set.mem_Ioi]; linarith⟩ : Set.Ioi (0 : Surreal.{0})))
    (fun a b hab => by
      simp only [Subtype.mk.injEq, add_left_inj] at hab
      simpa using hab)
  exact not_small_ordinal.{0, 0} this

theorem fitsStarOne : Fits ⋆ 1 := by
  refine ⟨?_, ?_⟩ <;> simp <;> game_cmp

theorem fitsOneYS : Fits 1 !{{⋆} | ∅} := by
  refine ⟨?_, ?_⟩ <;> simp <;> game_cmp

theorem notFits01 : ¬ Fits 0 (1 : IGame) := by
  rw [fits_zero_iff_equiv]; game_cmp

theorem one_lt_ofs (h : ∀ x ∈ ({1} : Set Surreal.{0}), ∀ y ∈ (∅ : Set Surreal.{0}), x < y) :
    (1 : Surreal.{0}) < @OfSets.ofSets _ _ _ (Player.cases {1} ∅) h (ss 1) smallEmpty :=
  Surreal.lt_ofSets_of_mem_left' (st := Player.cases {1} ∅) rfl

theorem ofs_lt_negone (h : ∀ x ∈ (∅ : Set Surreal.{0}), ∀ y ∈ ({-1} : Set Surreal.{0}), x < y) :
    @OfSets.ofSets _ _ _ (Player.cases ∅ {-1}) h smallEmpty (ss (-1)) < -1 :=
  Surreal.ofSets_lt_of_mem_right' (st := Player.cases ∅ {-1}) rfl

theorem zero_eq_ofs (h : ∀ x ∈ (∅ : Set Surreal.{0}), ∀ y ∈ (∅ : Set Surreal.{0}), x < y) :
    (0 : Surreal.{0}) = @OfSets.ofSets _ _ _ (Player.cases ∅ ∅) h smallEmpty smallEmpty :=
  Surreal.zero_def.trans (ofSets_eq_ofSets_cases _ _)


theorem starLe (z : IGame) [Numeric z] (h : 0 < z) : ⋆ ≤ z := by
  rw [le_iff_forall_lf]; refine ⟨?_, ?_⟩
  · intro a ha; simp at ha; subst ha; exact h.not_ge
  · intro b hb hbs
    have : 0 < b := h.trans (Numeric.lt_right hb)
    exact absurd (this.trans_le hbs) (by game_cmp)

theorem upLe (z : IGame) [Numeric z] (h : 0 < z) : ↑ ≤ z := by
  rw [le_iff_forall_lf]; refine ⟨?_, ?_⟩
  · intro a ha; simp at ha; subst ha; exact h.not_ge
  · intro b hb hbs
    have : Numeric b := Numeric.of_mem_moves hb
    have h1 := starLe b (h.trans (Numeric.lt_right hb))
    exact absurd (h1.trans hbs) (by game_cmp)

theorem nbddI : ¬ BddAbove ((fun x : Surreal.{0} => x.birthday + 1) '' Ioi 0) := by
  rintro ⟨B, hB⟩
  have hx : (0 : Surreal.{0}) < NatOrdinal.toSurreal (B + 1) := by
    rw [← NatOrdinal.toSurreal_zero]
    exact NatOrdinal.toSurreal.lt_iff_lt.2 (_root_.zero_le.trans_lt (lt_add_one B))
  have := hB (Set.mem_image_of_mem _ (Set.mem_Ioi.2 hx))
  simp only [Surreal.birthday_toSurreal] at this
  exact absurd this (not_le.2 ((lt_add_one B).trans (lt_add_one _)))

theorem nbddN : ¬ BddAbove ((fun x : Surreal.{0} => x.birthday + 1) '' Iio 0) := by
  rintro ⟨B, hB⟩
  have hx : -NatOrdinal.toSurreal (B + 1) < (0 : Surreal.{0}) := by
    have hp : (0 : Surreal.{0}) < NatOrdinal.toSurreal (B + 1) := by
      rw [← NatOrdinal.toSurreal_zero]
      exact NatOrdinal.toSurreal.lt_iff_lt.2 (_root_.zero_le.trans_lt (lt_add_one B))
    linarith
  have := hB (Set.mem_image_of_mem _ (Set.mem_Iio.2 hx))
  simp only [Surreal.birthday_neg, Surreal.birthday_toSurreal] at this
  exact absurd this (not_le.2 ((lt_add_one B).trans (lt_add_one _)))

end W2c4

open IGame Set W2c4

-- `IGame.Fits.antisymm` idx 3: necessary (x = 1, y = 0)
theorem c4_1 : ¬ drop0% IGame.Fits.antisymm 3 := fun h =>
  absurd (@h 1 0 (by simp [IGame.Fits])) (by game_cmp)

-- `IGame.Fits.congr` idx 3: necessary (x = 1, y = 0, z = 1)
theorem c4_2 : ¬ drop0% IGame.Fits.congr 3 := fun h => notFits01 (@h 1 0 1 (Fits.refl 1))

-- `IGame.fits_congr` idx 3: necessary (x = 1, y = 0, z = 1)
theorem c4_3 : ¬ drop0% IGame.fits_congr 3 := fun h => notFits01 ((@h 1 0 1).1 (Fits.refl 1))

-- `IGame.Fits.equiv_of_forall_moves` idx 3: necessary (x = 1, y = 0)
theorem c4_4 : ¬ drop0% IGame.Fits.equiv_of_forall_moves 3 := fun h =>
  absurd (@h 1 0 (by simp [IGame.Fits]) (by simp)) (by game_cmp)

-- `IGame.Fits.equiv_of_forall_moves` idx 4: necessary (x = -1, y = 0)
theorem c4_5 : ¬ drop0% IGame.Fits.equiv_of_forall_moves 4 := fun h =>
  absurd (@h (-1) 0 (by simp [IGame.Fits]) (by simp)) (by game_cmp)

-- `IGame.Fits.equiv_of_forall_moves_of_equiv` idx 3: necessary (x = 1, y = a = 0)
theorem c4_6 : ¬ drop0% IGame.Fits.equiv_of_forall_moves_of_equiv 3 := fun h =>
  absurd (@h 1 0 0 (by simp [IGame.Fits]) (by simp) (by simp)) (by game_cmp)

-- `IGame.Fits.equiv_of_forall_moves_of_equiv` idx 5: necessary (x = a = 1, y = 0)
theorem c4_7 : ¬ drop0% IGame.Fits.equiv_of_forall_moves_of_equiv 5 := fun h =>
  absurd (@h 1 0 1 .rfl (by simp [IGame.Fits]) (by simp)) (by game_cmp)

-- `IGame.Fits.equiv_of_forall_moves_of_equiv` idx 6: necessary (x = a = -1, y = 0)
theorem c4_8 : ¬ drop0% IGame.Fits.equiv_of_forall_moves_of_equiv 6 := fun h =>
  absurd (@h (-1) 0 (-1) .rfl (by simp [IGame.Fits]) (by simp)) (by game_cmp)

-- `IGame.Fits.equiv_of_forall_not_fits` idx 2: necessary (x = ⋆, y = 1)
theorem c4_9 : ¬ drop0% IGame.Fits.equiv_of_forall_not_fits 2 := fun h =>
  absurd (@h ⋆ 1 fitsStarOne (fun p z hz => by
    cases p <;> simp at hz <;> subst hz <;> exact notFits01)) (by game_cmp)

-- `IGame.Fits.equiv_of_forall_not_fits` idx 4: necessary (x = 1, y = 0)
theorem c4_10 : ¬ drop0% IGame.Fits.equiv_of_forall_not_fits 4 := fun h =>
  absurd (@h 1 0 _ (by simp [IGame.Fits])) (by game_cmp)

-- `IGame.Fits.equiv_of_forall_birthday_le` idx 2: necessary (x = ⋆, y = 1)
theorem c4_11 : ¬ drop0% IGame.Fits.equiv_of_forall_birthday_le 2 := fun h =>
  absurd (@h ⋆ 1 fitsStarOne (fun z _ hz => by
    rw [birthday_star, Order.one_le_iff_pos, pos_iff_ne_zero, Ne, IGame.birthday_eq_zero]
    rintro rfl; exact notFits01 hz)) (by game_cmp)

-- `IGame.Fits.equiv_of_forall_birthday_le` idx 4: necessary (x = 1, y = 0)
theorem c4_12 : ¬ drop0% IGame.Fits.equiv_of_forall_birthday_le 4 := fun h =>
  absurd (@h 1 0 _ (by simp [IGame.Fits])) (by game_cmp)

-- `IGame.Fits.exists_wsubposition_equiv` idx 2: necessary (x = ⋆, y = 1: subpositions of ⋆ are ⋆ and 0)
theorem c4_13 : ¬ drop0% IGame.Fits.exists_wsubposition_equiv 2 := fun h => by
  obtain ⟨z, hz, he⟩ := @h ⋆ 1 fitsStarOne
  rcases hz with rfl | hz
  · exact absurd he (by game_cmp)
  · rw [subposition_iff_exists] at hz
    obtain ⟨p, w, hw, hzw⟩ := hz
    cases p <;> simp at hw <;> subst hw <;>
    · rcases hzw with rfl | hzw
      · exact absurd he (by game_cmp)
      · rw [subposition_iff_exists] at hzw; simp at hzw

-- `IGame.Fits.exists_wsubposition_equiv` idx 3: necessary (x = 0, y = 1)
theorem c4_14 : ¬ drop0% IGame.Fits.exists_wsubposition_equiv 3 := fun h => by
  obtain ⟨z, hz, he⟩ := @h 0 1 _
  rcases hz with rfl | hz
  · exact absurd he (by game_cmp)
  · rw [subposition_iff_exists] at hz; simp at hz

-- `IGame.equiv_one_of_fits` idx 2: necessary (x = 0)
theorem c4_15 : ¬ drop0% IGame.equiv_one_of_fits 2 := fun h =>
  absurd (@h 0 (by simp [IGame.Fits])) (by game_cmp)

-- `Surreal.mk_eq_mk` idx 2: necessary (x = ⋆)
theorem c4_16 : ¬ indep0% Surreal.mk_eq_mk 2 := fun h => not_numeric_star (@h ⋆ 0 Numeric.zero)
-- `Surreal.mk_eq_mk` idx 3: necessary (y = ⋆)
theorem c4_17 : ¬ indep0% Surreal.mk_eq_mk 3 := fun h => not_numeric_star (@h 0 ⋆ Numeric.zero)
-- `Surreal.mk_eq` idx 2: necessary (x = {⋆ | } ≈ 0 = y, x not numeric)
theorem c4_18 : ¬ indep0% Surreal.mk_eq 2 := fun h =>
  notNumYS (@h !{{IGame.star} | ∅} 0 Numeric.zero (by game_cmp))
-- `Surreal.ind` idx 1: necessary (motive = False)
theorem c4_19 : ¬ drop0% Surreal.ind 1 := fun h => @h (fun _ => False) 0
-- `Surreal.mk_add` idx 3: necessary (y = ⋆)
theorem c4_20 : ¬ indep0% Surreal.mk_add 3 := fun h => not_numeric_star (@h 0 ⋆ Numeric.zero)
-- `Surreal.mk_sub` idx 2: necessary (x = ⋆)
theorem c4_21 : ¬ indep0% Surreal.mk_sub 2 := fun h => not_numeric_star (@h ⋆ 0 Numeric.zero)
-- `Surreal.mk_sub` idx 3: necessary (y = ⋆)
theorem c4_22 : ¬ indep0% Surreal.mk_sub 3 := fun h => not_numeric_star (@h 0 ⋆ Numeric.zero)
-- `Surreal.mk_le_mk` idx 2: necessary (x = ⋆)
theorem c4_23 : ¬ indep0% Surreal.mk_le_mk 2 := fun h => not_numeric_star (@h ⋆ 0 Numeric.zero)
-- `Surreal.mk_le_mk` idx 3: necessary (y = ⋆)
theorem c4_24 : ¬ indep0% Surreal.mk_le_mk 3 := fun h => not_numeric_star (@h 0 ⋆ Numeric.zero)
-- `Surreal.mk_lt_mk` idx 2: necessary (x = ⋆)
theorem c4_25 : ¬ indep0% Surreal.mk_lt_mk 2 := fun h => not_numeric_star (@h ⋆ 0 Numeric.zero)
-- `Surreal.mk_lt_mk` idx 3: necessary (y = ⋆)
theorem c4_26 : ¬ indep0% Surreal.mk_lt_mk 3 := fun h => not_numeric_star (@h 0 ⋆ Numeric.zero)

-- `IGame.Fits.gameBirthday_le` idx 2: necessary (x = y = ⋆)
theorem c4_27 : ¬ indep0% IGame.Fits.gameBirthday_le 2 := fun h =>
  not_numeric_star (@h ⋆ ⋆ (Fits.refl _))
-- `IGame.Fits.gameBirthday_lt` idx 2: necessary (x = ⋆, y = 1)
theorem c4_28 : ¬ indep0% IGame.Fits.gameBirthday_lt 2 := fun h =>
  not_numeric_star (@h ⋆ 1 fitsStarOne (by game_cmp))
-- `IGame.Fits.surrealBirthday_le` idx 2: necessary (x = ⋆, y = 1)
theorem c4_29 : ¬ indep0% IGame.Fits.surrealBirthday_le 2 := fun h =>
  not_numeric_star (@h ⋆ 1 Numeric.one fitsStarOne)
-- `IGame.Fits.surrealBirthday_le` idx 3: necessary (x = 1, y = {⋆ | })
theorem c4_30 : ¬ indep0% IGame.Fits.surrealBirthday_le 3 := fun h =>
  notNumYS (@h 1 _ Numeric.one fitsOneYS)
-- `IGame.Fits.surrealBirthday_lt` idx 2: necessary (x = ⋆, y = 1)
theorem c4_31 : ¬ indep0% IGame.Fits.surrealBirthday_lt 2 := fun h =>
  not_numeric_star (@h ⋆ 1 Numeric.one fitsStarOne (by game_cmp))
-- `IGame.Fits.surrealBirthday_lt` idx 3: necessary (x = 1, y = {⋆ | })
theorem c4_32 : ¬ indep0% IGame.Fits.surrealBirthday_lt 3 := fun h =>
  notNumYS (@h 1 _ Numeric.one fitsOneYS (by game_cmp))

-- `Surreal.ofSets_eq_mk'` idx 1: necessary (left set = all surreals)
theorem c4_33 : ¬ indep0% Surreal.ofSets_eq_mk' 1 := fun h =>
  notSmallUniv (@h (fun p => Player.cases univ ∅ p) smallEmpty (by simp))
-- `Surreal.ofSets_eq_mk'` idx 2: necessary (right set = all surreals)
theorem c4_34 : ¬ indep0% Surreal.ofSets_eq_mk' 2 := fun h =>
  notSmallUniv (@h (fun p => Player.cases ∅ univ p) smallEmpty (by simp))
-- `Surreal.ofSets_eq_mk'` idx 3: necessary (left {1}, right {0})
theorem c4_35 : ¬ indep0% Surreal.ofSets_eq_mk' 3 := fun h =>
  absurd (@h (fun p => Player.cases {1} {0} p) (ss 1) (ss 0) 1 rfl 0 rfl) (by simp)
-- `Surreal.ofSets_eq_mk` idx 2: necessary (s = all surreals)
theorem c4_36 : ¬ indep0% Surreal.ofSets_eq_mk 2 := fun h =>
  notSmallUniv (@h univ ∅ smallEmpty (by simp))
-- `Surreal.ofSets_eq_mk` idx 3: necessary (t = all surreals)
theorem c4_37 : ¬ indep0% Surreal.ofSets_eq_mk 3 := fun h =>
  notSmallUniv (@h ∅ univ smallEmpty (by simp))
-- `Surreal.toGame_ofSets'` idx 1: necessary (left set = all surreals)
theorem c4_38 : ¬ indep0% Surreal.toGame_ofSets' 1 := fun h =>
  notSmallUniv (@h (fun p => Player.cases univ ∅ p) smallEmpty (by simp))
-- `Surreal.toGame_ofSets'` idx 2: necessary (right set = all surreals)
theorem c4_39 : ¬ indep0% Surreal.toGame_ofSets' 2 := fun h =>
  notSmallUniv (@h (fun p => Player.cases ∅ univ p) smallEmpty (by simp))
-- `Surreal.toGame_ofSets'` idx 3: necessary (left {1}, right {0})
theorem c4_40 : ¬ indep0% Surreal.toGame_ofSets' 3 := fun h =>
  absurd (@h (fun p => Player.cases {1} {0} p) (ss 1) (ss 0) 1 rfl 0 rfl) (by simp)
-- `Surreal.toGame_ofSets` idx 2: necessary (s = all surreals)
theorem c4_41 : ¬ indep0% Surreal.toGame_ofSets 2 := fun h =>
  notSmallUniv (@h univ ∅ smallEmpty (by simp))
-- `Surreal.toGame_ofSets` idx 3: necessary (t = all surreals)
theorem c4_42 : ¬ indep0% Surreal.toGame_ofSets 3 := fun h =>
  notSmallUniv (@h ∅ univ smallEmpty (by simp))
-- `Surreal.mk_ofSets'` idx 1: necessary (left set = all games)
theorem c4_43 : ¬ indep0% Surreal.mk_ofSets' 1 := fun h =>
  notSmallIGame (@h (fun p => Player.cases univ ∅ p) se)
-- `Surreal.mk_ofSets'` idx 2: necessary (right set = all games)
theorem c4_44 : ¬ indep0% Surreal.mk_ofSets' 2 := fun h =>
  notSmallIGame (@h (fun p => Player.cases ∅ univ p) se)
-- `Surreal.mk_ofSets'` idx 3: necessary (left {⋆}, right ∅)
theorem c4_45 : ¬ indep0% Surreal.mk_ofSets' 3 := fun h =>
  notNumYS (@h (fun p => Player.cases {⋆} ∅ p) (small_single _) se)
-- `Surreal.mk_ofSets` idx 2: necessary (s = all games)
theorem c4_46 : ¬ indep0% Surreal.mk_ofSets 2 := fun h => notSmallIGame (@h univ ∅ se)
-- `Surreal.mk_ofSets` idx 3: necessary (t = all games)
theorem c4_47 : ¬ indep0% Surreal.mk_ofSets 3 := fun h => notSmallIGame (@h ∅ univ se)
-- `Surreal.mk_ofSets` idx 4: necessary (s = {⋆}, t = ∅)
theorem c4_48 : ¬ indep0% Surreal.mk_ofSets 4 := fun h => notNumYS (@h {⋆} ∅ (small_single _) se)

-- `Surreal.lt_ofSets_of_mem_left'` idx 1: necessary (left set = all surreals, x = 0)
theorem c4_49 : ¬ indep0% Surreal.lt_ofSets_of_mem_left' 1 := fun h =>
  notSmallUniv (@h (fun p => Player.cases univ ∅ p) smallEmpty (by simp) 0 trivial)
-- `Surreal.lt_ofSets_of_mem_left'` idx 2: necessary (left {0}, right = positive surreals)
theorem c4_50 : ¬ indep0% Surreal.lt_ofSets_of_mem_left' 2 := fun h =>
  notSmallIoi (@h (fun p => Player.cases {0} (Ioi 0) p) (ss 0) (by simp) 0 rfl)
-- `Surreal.lt_ofSets_of_mem_left'` idx 3: necessary (left {1}, right {0})
theorem c4_51 : ¬ indep0% Surreal.lt_ofSets_of_mem_left' 3 := fun h =>
  absurd (@h (fun p => Player.cases {1} {0} p) (ss 1) (ss 0) 1 rfl 1 rfl 0 rfl) (by simp)
-- `Surreal.lt_ofSets_of_mem_left'` idx 5: necessary (empty sets, x = the cut itself)
theorem c4_52 : ¬ drop0% Surreal.lt_ofSets_of_mem_left' 5 := fun h =>
  lt_irrefl _ (@h (fun _ => ∅) smallEmpty smallEmpty (by simp) _)
-- `Surreal.ofSets_lt_of_mem_right'` idx 1: necessary (left = negative surreals, right {0})
theorem c4_53 : ¬ indep0% Surreal.ofSets_lt_of_mem_right' 1 := fun h =>
  notSmallIio (@h (fun p => Player.cases (Iio 0) {0} p) (ss 0) (by simp) 0 rfl)
-- `Surreal.ofSets_lt_of_mem_right'` idx 2: necessary (right set = all surreals)
theorem c4_54 : ¬ indep0% Surreal.ofSets_lt_of_mem_right' 2 := fun h =>
  notSmallUniv (@h (fun p => Player.cases ∅ univ p) smallEmpty (by simp) 0 trivial)
-- `Surreal.ofSets_lt_of_mem_right'` idx 3: necessary (left {1}, right {0})
theorem c4_55 : ¬ indep0% Surreal.ofSets_lt_of_mem_right' 3 := fun h =>
  absurd (@h (fun p => Player.cases {1} {0} p) (ss 1) (ss 0) 0 rfl 1 rfl 0 rfl) (by simp)
-- `Surreal.ofSets_lt_of_mem_right'` idx 5: necessary (empty sets, x = the cut itself)
theorem c4_56 : ¬ drop0% Surreal.ofSets_lt_of_mem_right' 5 := fun h =>
  lt_irrefl _ (@h (fun _ => ∅) smallEmpty smallEmpty (by simp) _)
-- `Surreal.lt_ofSets_of_mem_left` idx 2: necessary (s = all surreals)
theorem c4_57 : ¬ indep0% Surreal.lt_ofSets_of_mem_left 2 := fun h =>
  notSmallUniv (@h univ ∅ smallEmpty (by simp) 0 trivial)
-- `Surreal.lt_ofSets_of_mem_left` idx 3: necessary (s = {0}, t = positive surreals)
theorem c4_58 : ¬ indep0% Surreal.lt_ofSets_of_mem_left 3 := fun h =>
  notSmallIoi (@h {0} (Ioi 0) (ss 0) (by simp) 0 rfl)
-- `Surreal.lt_ofSets_of_mem_left` idx 4: necessary (s = {1}, t = {0})
theorem c4_59 : ¬ indep0% Surreal.lt_ofSets_of_mem_left 4 := fun h =>
  absurd (@h {1} {0} (ss 1) (ss 0) 1 rfl 1 rfl 0 rfl) (by simp)
-- `Surreal.lt_ofSets_of_mem_left` idx 6: necessary (s = t = ∅, x = the cut itself)
theorem c4_60 : ¬ drop0% Surreal.lt_ofSets_of_mem_left 6 := fun h =>
  lt_irrefl _ (@h ∅ ∅ smallEmpty smallEmpty (by simp) _)
-- `Surreal.ofSets_lt_of_mem_right` idx 2: necessary (s = negative surreals, t = {0})
theorem c4_61 : ¬ indep0% Surreal.ofSets_lt_of_mem_right 2 := fun h =>
  notSmallIio (@h (Iio 0) {0} (ss 0) (by simp) 0 rfl)
-- `Surreal.ofSets_lt_of_mem_right` idx 3: necessary (t = all surreals)
theorem c4_62 : ¬ indep0% Surreal.ofSets_lt_of_mem_right 3 := fun h =>
  notSmallUniv (@h ∅ univ smallEmpty (by simp) 0 trivial)
-- `Surreal.ofSets_lt_of_mem_right` idx 4: necessary (s = {1}, t = {0})
theorem c4_63 : ¬ indep0% Surreal.ofSets_lt_of_mem_right 4 := fun h =>
  absurd (@h {1} {0} (ss 1) (ss 0) 0 rfl 1 rfl 0 rfl) (by simp)
-- `Surreal.ofSets_lt_of_mem_right` idx 6: necessary (s = t = ∅, x = the cut itself)
theorem c4_64 : ¬ drop0% Surreal.ofSets_lt_of_mem_right 6 := fun h =>
  lt_irrefl _ (@h ∅ ∅ smallEmpty smallEmpty (by simp) _)

-- `Surreal.ofSets_le_ofSets_iff'` idx 3: necessary (right set of the first cut = all surreals)
theorem c4_65 : ¬ indep0% Surreal.ofSets_le_ofSets_iff' 3 := fun h =>
  notSmallUniv (@h (fun p => Player.cases ∅ univ p) (fun _ => ∅) smallEmpty smallEmpty smallEmpty
    (by simp) (by simp))
-- `Surreal.ofSets_le_ofSets_iff'` idx 4: necessary (left set of the second cut = all surreals)
theorem c4_66 : ¬ indep0% Surreal.ofSets_le_ofSets_iff' 4 := fun h =>
  notSmallUniv (@h (fun _ => ∅) (fun p => Player.cases univ ∅ p) smallEmpty smallEmpty smallEmpty
    (by simp) (by simp))
-- `Surreal.ofSets_le_ofSets_iff'` idx 5: necessary (right set of the second cut = all surreals)
theorem c4_67 : ¬ indep0% Surreal.ofSets_le_ofSets_iff' 5 := fun h =>
  notSmallUniv (@h (fun _ => ∅) (fun p => Player.cases ∅ univ p) smallEmpty smallEmpty smallEmpty
    (by simp) (by simp))
-- `Surreal.ofSets_le_ofSets_iff'` idx 6: necessary (first cut {1 | 0})
theorem c4_68 : ¬ indep0% Surreal.ofSets_le_ofSets_iff' 6 := fun h =>
  absurd (@h (fun p => Player.cases {1} {0} p) (fun _ => ∅) (ss 1) (ss 0) smallEmpty smallEmpty
    (by simp) 1 rfl 0 rfl) (by simp)
-- `Surreal.ofSets_le_ofSets_iff'` idx 7: necessary (second cut {1 | 0})
theorem c4_69 : ¬ indep0% Surreal.ofSets_le_ofSets_iff' 7 := fun h =>
  absurd (@h (fun _ => ∅) (fun p => Player.cases {1} {0} p) smallEmpty smallEmpty (ss 1) (ss 0)
    (by simp) 1 rfl 0 rfl) (by simp)
-- `Surreal.ofSets_lt_ofSets_iff'` idx 2: necessary (left set of the first cut = all surreals)
theorem c4_70 : ¬ indep0% Surreal.ofSets_lt_ofSets_iff' 2 := fun h =>
  notSmallUniv (@h (fun p => Player.cases univ ∅ p) (fun _ => ∅) smallEmpty smallEmpty smallEmpty
    (by simp) (by simp))
-- `Surreal.ofSets_lt_ofSets_iff'` idx 3: necessary (right set of the first cut = all surreals)
theorem c4_71 : ¬ indep0% Surreal.ofSets_lt_ofSets_iff' 3 := fun h =>
  notSmallUniv (@h (fun p => Player.cases ∅ univ p) (fun _ => ∅) smallEmpty smallEmpty smallEmpty
    (by simp) (by simp))
-- `Surreal.ofSets_lt_ofSets_iff'` idx 4: necessary (left set of the second cut = all surreals)
theorem c4_72 : ¬ indep0% Surreal.ofSets_lt_ofSets_iff' 4 := fun h =>
  notSmallUniv (@h (fun _ => ∅) (fun p => Player.cases univ ∅ p) smallEmpty smallEmpty smallEmpty
    (by simp) (by simp))
-- `Surreal.ofSets_lt_ofSets_iff'` idx 5: necessary (right set of the second cut = all surreals)
theorem c4_73 : ¬ indep0% Surreal.ofSets_lt_ofSets_iff' 5 := fun h =>
  notSmallUniv (@h (fun _ => ∅) (fun p => Player.cases ∅ univ p) smallEmpty smallEmpty smallEmpty
    (by simp) (by simp))
-- `Surreal.ofSets_lt_ofSets_iff'` idx 6: necessary (first cut {1 | 0})
theorem c4_74 : ¬ indep0% Surreal.ofSets_lt_ofSets_iff' 6 := fun h =>
  absurd (@h (fun p => Player.cases {1} {0} p) (fun _ => ∅) (ss 1) (ss 0) smallEmpty smallEmpty
    (by simp) 1 rfl 0 rfl) (by simp)
-- `Surreal.ofSets_lt_ofSets_iff'` idx 7: necessary (second cut {1 | 0})
theorem c4_75 : ¬ indep0% Surreal.ofSets_lt_ofSets_iff' 7 := fun h =>
  absurd (@h (fun _ => ∅) (fun p => Player.cases {1} {0} p) smallEmpty smallEmpty (ss 1) (ss 0)
    (by simp) 1 rfl 0 rfl) (by simp)
-- `Surreal.ofSets_le_ofSets_iff` idx 4: necessary (s₁ = all surreals)
theorem c4_76 : ¬ indep0% Surreal.ofSets_le_ofSets_iff 4 := fun h =>
  notSmallUniv (@h univ ∅ ∅ ∅ smallEmpty smallEmpty smallEmpty (by simp) (by simp))
-- `Surreal.ofSets_le_ofSets_iff` idx 5: necessary (t₁ = all surreals)
theorem c4_77 : ¬ indep0% Surreal.ofSets_le_ofSets_iff 5 := fun h =>
  notSmallUniv (@h ∅ univ ∅ ∅ smallEmpty smallEmpty smallEmpty (by simp) (by simp))
-- `Surreal.ofSets_le_ofSets_iff` idx 6: necessary (s₂ = all surreals)
theorem c4_78 : ¬ indep0% Surreal.ofSets_le_ofSets_iff 6 := fun h =>
  notSmallUniv (@h ∅ ∅ univ ∅ smallEmpty smallEmpty smallEmpty (by simp) (by simp))
-- `Surreal.ofSets_le_ofSets_iff` idx 7: necessary (t₂ = all surreals)
theorem c4_79 : ¬ indep0% Surreal.ofSets_le_ofSets_iff 7 := fun h =>
  notSmallUniv (@h ∅ ∅ ∅ univ smallEmpty smallEmpty smallEmpty (by simp) (by simp))
-- `Surreal.ofSets_le_ofSets_iff` idx 8: necessary (s₁ = {1}, t₁ = {0})
theorem c4_80 : ¬ indep0% Surreal.ofSets_le_ofSets_iff 8 := fun h =>
  absurd (@h {1} {0} ∅ ∅ (ss 1) (ss 0) smallEmpty smallEmpty (by simp) 1 rfl 0 rfl) (by simp)
-- `Surreal.ofSets_le_ofSets_iff` idx 9: necessary (s₂ = {1}, t₂ = {0})
theorem c4_81 : ¬ indep0% Surreal.ofSets_le_ofSets_iff 9 := fun h =>
  absurd (@h ∅ ∅ {1} {0} smallEmpty smallEmpty (ss 1) (ss 0) (by simp) 1 rfl 0 rfl) (by simp)
-- `Surreal.ofSets_lt_ofSets_iff` idx 4: necessary (s₁ = all surreals)
theorem c4_82 : ¬ indep0% Surreal.ofSets_lt_ofSets_iff 4 := fun h =>
  notSmallUniv (@h univ ∅ ∅ ∅ smallEmpty smallEmpty smallEmpty (by simp) (by simp))
-- `Surreal.ofSets_lt_ofSets_iff` idx 5: necessary (t₁ = all surreals)
theorem c4_83 : ¬ indep0% Surreal.ofSets_lt_ofSets_iff 5 := fun h =>
  notSmallUniv (@h ∅ univ ∅ ∅ smallEmpty smallEmpty smallEmpty (by simp) (by simp))
-- `Surreal.ofSets_lt_ofSets_iff` idx 6: necessary (s₂ = all surreals)
theorem c4_84 : ¬ indep0% Surreal.ofSets_lt_ofSets_iff 6 := fun h =>
  notSmallUniv (@h ∅ ∅ univ ∅ smallEmpty smallEmpty smallEmpty (by simp) (by simp))
-- `Surreal.ofSets_lt_ofSets_iff` idx 7: necessary (t₂ = all surreals)
theorem c4_85 : ¬ indep0% Surreal.ofSets_lt_ofSets_iff 7 := fun h =>
  notSmallUniv (@h ∅ ∅ ∅ univ smallEmpty smallEmpty smallEmpty (by simp) (by simp))
-- `Surreal.ofSets_lt_ofSets_iff` idx 8: necessary (s₁ = {1}, t₁ = {0})
theorem c4_86 : ¬ indep0% Surreal.ofSets_lt_ofSets_iff 8 := fun h =>
  absurd (@h {1} {0} ∅ ∅ (ss 1) (ss 0) smallEmpty smallEmpty (by simp) 1 rfl 0 rfl) (by simp)
-- `Surreal.ofSets_lt_ofSets_iff` idx 9: necessary (s₂ = {1}, t₂ = {0})
theorem c4_87 : ¬ indep0% Surreal.ofSets_lt_ofSets_iff 9 := fun h =>
  absurd (@h ∅ ∅ {1} {0} smallEmpty smallEmpty (ss 1) (ss 0) (by simp) 1 rfl 0 rfl) (by simp)

-- `Surreal.birthday_ofSets_le_of_btwn'` idx 3: necessary (right set = positive surreals, z = 0)
theorem c4_88 : ¬ indep0% Surreal.birthday_ofSets_le_of_btwn' 3 := fun h =>
  notSmallIoi (@h (fun p => Player.cases ∅ (Ioi 0) p) 0 smallEmpty (by simp) (by simp) (fun _ hx => hx))
-- `Surreal.birthday_ofSets_le_of_btwn'` idx 5: necessary (left {1}, right ∅, z = 0)
theorem c4_89 : ¬ drop0% Surreal.birthday_ofSets_le_of_btwn' 5 := fun h => by
  have := @h (Player.cases {1} ∅) 0 (ss 1) smallEmpty (by simp) (by simp)
  rw [Surreal.birthday_zero, nonpos_iff_eq_zero, Surreal.birthday_eq_zero] at this
  exact absurd ((one_lt_ofs _).trans_eq this) (by simp)
-- `Surreal.birthday_ofSets_le_of_btwn'` idx 6: necessary (left ∅, right {-1}, z = 0)
theorem c4_90 : ¬ drop0% Surreal.birthday_ofSets_le_of_btwn' 6 := fun h => by
  have := @h (Player.cases ∅ {-1}) 0 smallEmpty (ss (-1)) (by simp) (by simp)
  rw [Surreal.birthday_zero, nonpos_iff_eq_zero, Surreal.birthday_eq_zero] at this
  exact absurd (this.symm.trans_lt (ofs_lt_negone _)) (by simp)
-- `Surreal.birthday_ofSets_lt_of_btwn'` idx 2: necessary (left = negative surreals, z = 0)
theorem c4_91 : ¬ indep0% Surreal.birthday_ofSets_lt_of_btwn' 2 := fun h =>
  notSmallIio (@h (fun p => Player.cases (Iio 0) ∅ p) 0 smallEmpty (by simp) (fun _ hx => hx) (by simp))
-- `Surreal.birthday_ofSets_lt_of_btwn'` idx 3: necessary (right = positive surreals, z = 0)
theorem c4_92 : ¬ indep0% Surreal.birthday_ofSets_lt_of_btwn' 3 := fun h =>
  notSmallIoi (@h (fun p => Player.cases ∅ (Ioi 0) p) 0 smallEmpty (by simp) (by simp) (fun _ hx => hx))
-- `Surreal.birthday_ofSets_lt_of_btwn'` idx 5: necessary (left {1}, right ∅, z = 0)
theorem c4_93 : ¬ drop0% Surreal.birthday_ofSets_lt_of_btwn' 5 := fun h => by
  have := @h (Player.cases {1} ∅) 0 (ss 1) smallEmpty (by simp) (by simp)
    (fun e => absurd ((one_lt_ofs _).trans_eq e) (by simp))
  rw [Surreal.birthday_zero] at this
  exact not_lt_zero' this
-- `Surreal.birthday_ofSets_lt_of_btwn'` idx 6: necessary (left ∅, right {-1}, z = 0)
theorem c4_94 : ¬ drop0% Surreal.birthday_ofSets_lt_of_btwn' 6 := fun h => by
  have := @h (Player.cases ∅ {-1}) 0 smallEmpty (ss (-1)) (by simp) (by simp)
    (fun e => absurd (e.symm.trans_lt (ofs_lt_negone _)) (by simp))
  rw [Surreal.birthday_zero] at this
  exact not_lt_zero' this
-- `Surreal.birthday_ofSets_le_of_btwn` idx 3: necessary (s = negative surreals, z = 0)
theorem c4_95 : ¬ indep0% Surreal.birthday_ofSets_le_of_btwn 3 := fun h =>
  notSmallIio (@h (Iio 0) ∅ 0 smallEmpty (by simp) (fun _ hx => hx) (by simp))
-- `Surreal.birthday_ofSets_le_of_btwn` idx 4: necessary (t = positive surreals, z = 0)
theorem c4_96 : ¬ indep0% Surreal.birthday_ofSets_le_of_btwn 4 := fun h =>
  notSmallIoi (@h ∅ (Ioi 0) 0 smallEmpty (by simp) (by simp) (fun _ hx => hx))
-- `Surreal.birthday_ofSets_le_of_btwn` idx 6: necessary (s = {1}, t = ∅, z = 0)
theorem c4_97 : ¬ drop0% Surreal.birthday_ofSets_le_of_btwn 6 := fun h => by
  have := @h {1} ∅ 0 (ss 1) smallEmpty (by simp) (by simp)
  rw [Surreal.birthday_zero, nonpos_iff_eq_zero, Surreal.birthday_eq_zero] at this
  exact absurd ((one_lt_ofs _).trans_eq this) (by simp)
-- `Surreal.birthday_ofSets_le_of_btwn` idx 7: necessary (s = ∅, t = {-1}, z = 0)
theorem c4_98 : ¬ drop0% Surreal.birthday_ofSets_le_of_btwn 7 := fun h => by
  have := @h ∅ {-1} 0 smallEmpty (ss (-1)) (by simp) (by simp)
  rw [Surreal.birthday_zero, nonpos_iff_eq_zero, Surreal.birthday_eq_zero] at this
  exact absurd (this.symm.trans_lt (ofs_lt_negone _)) (by simp)
-- `Surreal.birthday_ofSets_lt_of_btwn` idx 3: necessary (s = negative surreals, z = 0)
theorem c4_99 : ¬ indep0% Surreal.birthday_ofSets_lt_of_btwn 3 := fun h =>
  notSmallIio (@h (Iio 0) ∅ 0 smallEmpty (by simp) (fun _ hx => hx) (by simp))
-- `Surreal.birthday_ofSets_lt_of_btwn` idx 4: necessary (t = positive surreals, z = 0)
theorem c4_100 : ¬ indep0% Surreal.birthday_ofSets_lt_of_btwn 4 := fun h =>
  notSmallIoi (@h ∅ (Ioi 0) 0 smallEmpty (by simp) (by simp) (fun _ hx => hx))
-- `Surreal.birthday_ofSets_lt_of_btwn` idx 6: necessary (s = {1}, t = ∅, z = 0)
theorem c4_101 : ¬ drop0% Surreal.birthday_ofSets_lt_of_btwn 6 := fun h => by
  have := @h {1} ∅ 0 (ss 1) smallEmpty (by simp) (by simp)
    (fun e => absurd ((one_lt_ofs _).trans_eq e) (by simp))
  rw [Surreal.birthday_zero] at this
  exact not_lt_zero' this
-- `Surreal.birthday_ofSets_lt_of_btwn` idx 7: necessary (s = ∅, t = {-1}, z = 0)
theorem c4_102 : ¬ drop0% Surreal.birthday_ofSets_lt_of_btwn 7 := fun h => by
  have := @h ∅ {-1} 0 smallEmpty (ss (-1)) (by simp) (by simp)
    (fun e => absurd (e.symm.trans_lt (ofs_lt_negone _)) (by simp))
  rw [Surreal.birthday_zero] at this
  exact not_lt_zero' this
-- `Surreal.ofSets_eq_of_forall_birthday_le'` idx 2: necessary (left = negative surreals, z = 0)
theorem c4_103 : ¬ indep0% Surreal.ofSets_eq_of_forall_birthday_le' 2 := fun h =>
  notSmallIio (@h (fun p => Player.cases (Iio 0) ∅ p) 0 smallEmpty (by simp) (fun _ hx => hx) (by simp)
    (fun w _ _ => by simp))
-- `Surreal.ofSets_eq_of_forall_birthday_le'` idx 3: necessary (right = positive surreals, z = 0)
theorem c4_104 : ¬ indep0% Surreal.ofSets_eq_of_forall_birthday_le' 3 := fun h =>
  notSmallIoi (@h (fun p => Player.cases ∅ (Ioi 0) p) 0 smallEmpty (by simp) (by simp) (fun _ hx => hx)
    (fun w _ _ => by simp))
-- `Surreal.ofSets_eq_of_forall_birthday_le'` idx 5: necessary (left {1}, right ∅, z = 0)
theorem c4_105 : ¬ drop0% Surreal.ofSets_eq_of_forall_birthday_le' 5 := fun h =>
  absurd ((one_lt_ofs _).trans_eq
    (@h (Player.cases {1} ∅) 0 (ss 1) smallEmpty (by simp) (by simp) (fun w _ _ => by simp))) (by simp)
-- `Surreal.ofSets_eq_of_forall_birthday_le'` idx 6: necessary (left ∅, right {-1}, z = 0)
theorem c4_106 : ¬ drop0% Surreal.ofSets_eq_of_forall_birthday_le' 6 := fun h =>
  absurd ((@h (Player.cases ∅ {-1}) 0 smallEmpty (ss (-1)) (by simp) (by simp)
    (fun w _ _ => by simp)).symm.trans_lt (ofs_lt_negone _)) (by simp)
-- `Surreal.ofSets_eq_of_forall_birthday_le'` idx 7: necessary (empty sets, z = 1)
theorem c4_107 : ¬ drop0% Surreal.ofSets_eq_of_forall_birthday_le' 7 := fun h =>
  zero_ne_one ((zero_eq_ofs _).trans (@h (Player.cases ∅ ∅) 1 smallEmpty smallEmpty (by simp) (by simp) (by simp)))
-- `Surreal.ofSets_eq_of_forall_birthday_le` idx 3: necessary (s = negative surreals, z = 0)
theorem c4_108 : ¬ indep0% Surreal.ofSets_eq_of_forall_birthday_le 3 := fun h =>
  notSmallIio (@h (Iio 0) ∅ 0 smallEmpty (by simp) (fun _ hx => hx) (by simp) (fun w _ _ => by simp))
-- `Surreal.ofSets_eq_of_forall_birthday_le` idx 4: necessary (t = positive surreals, z = 0)
theorem c4_109 : ¬ indep0% Surreal.ofSets_eq_of_forall_birthday_le 4 := fun h =>
  notSmallIoi (@h ∅ (Ioi 0) 0 smallEmpty (by simp) (by simp) (fun _ hx => hx) (fun w _ _ => by simp))
-- `Surreal.ofSets_eq_of_forall_birthday_le` idx 6: necessary (s = {1}, t = ∅, z = 0)
theorem c4_110 : ¬ drop0% Surreal.ofSets_eq_of_forall_birthday_le 6 := fun h =>
  absurd ((one_lt_ofs _).trans_eq
    (@h {1} ∅ 0 (ss 1) smallEmpty (by simp) (by simp) (fun w _ _ => by simp))) (by simp)
-- `Surreal.ofSets_eq_of_forall_birthday_le` idx 7: necessary (s = ∅, t = {-1}, z = 0)
theorem c4_111 : ¬ drop0% Surreal.ofSets_eq_of_forall_birthday_le 7 := fun h =>
  absurd ((@h ∅ {-1} 0 smallEmpty (ss (-1)) (by simp) (by simp)
    (fun w _ _ => by simp)).symm.trans_lt (ofs_lt_negone _)) (by simp)
-- `Surreal.ofSets_eq_of_forall_birthday_le` idx 8: necessary (s = t = ∅, z = 1)
theorem c4_112 : ¬ drop0% Surreal.ofSets_eq_of_forall_birthday_le 8 := fun h =>
  zero_ne_one ((zero_eq_ofs _).trans (@h ∅ ∅ 1 smallEmpty smallEmpty (by simp) (by simp) (by simp)))
-- `Surreal.birthday_ofSets_le'` idx 2: necessary (right set = all surreals)
theorem c4_113 : ¬ indep0% Surreal.birthday_ofSets_le' 2 := fun h =>
  notSmallUniv (@h (fun p => Player.cases ∅ univ p) smallEmpty (by simp))
-- `Surreal.birthday_ofSets_le'` idx 3: necessary (left {1}, right {0})
theorem c4_114 : ¬ indep0% Surreal.birthday_ofSets_le' 3 := fun h =>
  absurd (@h (fun p => Player.cases {1} {0} p) (ss 1) (ss 0) 1 rfl 0 rfl) (by simp)
-- `Surreal.birthday_ofSets_le` idx 3: necessary (t = all surreals)
theorem c4_115 : ¬ indep0% Surreal.birthday_ofSets_le 3 := fun h =>
  notSmallUniv (@h ∅ univ smallEmpty (by simp))

-- `Surreal.Cut.player_infLeft` idx 1: necessary (s = all surreals)
theorem c4_116 : ¬ indep0% Surreal.Cut.player_infLeft 1 := fun h => notSmallUniv (h univ)
-- `Surreal.Cut.player_supRight` idx 1: necessary (s = all surreals)
theorem c4_117 : ¬ indep0% Surreal.Cut.player_supRight 1 := fun h => notSmallUniv (h univ)
-- `Surreal.Cut.exists_of_player_eq_left` idx 2: necessary (x = ⊥, whose player is right)
theorem c4_118 : ¬ drop0% Surreal.Cut.exists_of_player_eq_left 2 := fun h => by
  obtain ⟨s, hs, e⟩ := @h ⊥ Surreal.Cut.Small.bot
  have key : ∀ y (_ : sInf (Surreal.Cut.leftSurreal '' s) = y) [y.Small], y.player = .left := by
    intro y e _; subst e; exact Surreal.Cut.player_infLeft s
  have := key ⊥ e
  rw [Surreal.Cut.player_bot] at this
  exact absurd this (by decide)
-- `Surreal.Cut.exists_of_player_eq_right` idx 2: necessary (x = ⊤, whose player is left)
theorem c4_119 : ¬ drop0% Surreal.Cut.exists_of_player_eq_right 2 := fun h => by
  obtain ⟨s, hs, e⟩ := @h ⊤ Surreal.Cut.Small.top
  have key : ∀ y (_ : sSup (Surreal.Cut.rightSurreal '' s) = y) [y.Small], y.player = .right := by
    intro y e _; subst e; exact Surreal.Cut.player_supRight s
  have := key ⊤ e
  rw [Surreal.Cut.player_top] at this
  exact absurd this (by decide)


-- `IGame.Numeric.exists_between` idx 3: necessary (x = 0, y = ↑: every positive number is ≥ ↑)
theorem c4_120 : ¬ drop0% IGame.Numeric.exists_between 3 := fun h => by
  obtain ⟨z, hz, h1, h2⟩ := @h 0 IGame.up Numeric.zero (by game_cmp)
  exact h2.not_ge (@upLe z hz h1)

-- `IGame.Numeric.exists_between` idx 2: necessary (x = ↓, y = 0: every negative number is ≤ ↓)
theorem c4_121 : ¬ drop0% IGame.Numeric.exists_between 2 := fun h => by
  obtain ⟨z, hz, h1, h2⟩ := @h IGame.down 0 Numeric.zero (by game_cmp)
  have h3 : 0 < -z := by simpa using h2
  have := IGame.neg_le_neg_iff.2 (@upLe (-z) (Numeric.neg z) h3)
  simp only [neg_neg, neg_up] at this
  exact h1.not_ge this

-- `Surreal.Cut.birthday_sInf_leftSurreal_le'` idx 1: necessary (s = positive surreals: the cut is rightSurreal 0 of birthday 1, the unbounded sSup is junk 0)
theorem c4_122 : ¬ drop0% Surreal.Cut.birthday_sInf_leftSurreal_le' 1 := fun h => by
  have := h (Ioi 0)
  have e1 : sInf (Surreal.Cut.leftSurreal '' Ioi (0 : Surreal.{0})) = Surreal.Cut.rightSurreal 0 :=
    Surreal.Cut.sInf_leftSurreal_right (Surreal.Cut.rightSurreal 0)
  rw [e1, Surreal.Cut.birthday_rightSurreal, Surreal.birthday_zero, csSup_of_not_bddAbove nbddI,
    csSup_empty] at this
  simp at this

-- `Surreal.Cut.birthday_sSup_rightSurreal_le'` idx 1: necessary (s = negative surreals: the cut is leftSurreal 0 of birthday 1, the unbounded sSup is junk 0)
theorem c4_123 : ¬ drop0% Surreal.Cut.birthday_sSup_rightSurreal_le' 1 := fun h => by
  have := h (Iio 0)
  have e1 : sSup (Surreal.Cut.rightSurreal '' Iio (0 : Surreal.{0})) = Surreal.Cut.leftSurreal 0 :=
    Surreal.Cut.sSup_rightSurreal_left (Surreal.Cut.leftSurreal 0)
  rw [e1, Surreal.Cut.birthday_leftSurreal, Surreal.birthday_zero, csSup_of_not_bddAbove nbddN,
    csSup_empty] at this
  simp at this


-- `Surreal.Cut.birthday_iInf_leftSurreal_le'` idx 2: necessary (ι = positive surreals (universe 1), f = coercion: as for the sInf version)
theorem c4_124 : ¬ dropU% Surreal.Cut.birthday_iInf_leftSurreal_le' 2 [0, 1] := fun h => by
  have := @h (Ioi (0 : Surreal.{0})) Subtype.val
  rw [← sInf_image'] at this
  have nb : ¬ BddAbove (range fun i : Ioi (0 : Surreal.{0}) => (i : Surreal).birthday + 1) := by
    have h0 := nbddI; rwa [Set.image_eq_range] at h0
  have e1 : sInf (Surreal.Cut.leftSurreal '' Ioi (0 : Surreal.{0})) = Surreal.Cut.rightSurreal 0 :=
    Surreal.Cut.sInf_leftSurreal_right (Surreal.Cut.rightSurreal 0)
  rw [e1, Surreal.Cut.birthday_rightSurreal, Surreal.birthday_zero, ciSup_of_not_bddAbove nb,
    csSup_empty] at this
  simp at this

-- `Surreal.Cut.birthday_iSup_rightSurreal_le'` idx 2: necessary (ι = negative surreals (universe 1), f = coercion: as for the sSup version)
theorem c4_125 : ¬ dropU% Surreal.Cut.birthday_iSup_rightSurreal_le' 2 [0, 1] := fun h => by
  have := @h (Iio (0 : Surreal.{0})) Subtype.val
  rw [← sSup_image'] at this
  have nb : ¬ BddAbove (range fun i : Iio (0 : Surreal.{0}) => (i : Surreal).birthday + 1) := by
    have h0 := nbddN; rwa [Set.image_eq_range] at h0
  have e1 : sSup (Surreal.Cut.rightSurreal '' Iio (0 : Surreal.{0})) = Surreal.Cut.leftSurreal 0 :=
    Surreal.Cut.sSup_rightSurreal_left (Surreal.Cut.leftSurreal 0)
  rw [e1, Surreal.Cut.birthday_leftSurreal, Surreal.birthday_zero, ciSup_of_not_bddAbove nb,
    csSup_empty] at this
  simp at this

namespace W2c4
open Set Surreal Surreal.Cut SignExpansion

open scoped Classical in
noncomputable def altS : SignExpansion.{0} where
  sign o := if Order.IsSuccPrelimit (NatOrdinal.val o) then 1 else -1
  isUpperSet_preimage_singleton_zero' := by
    convert isUpperSet_empty using 1
    ext o
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    split_ifs <;> decide

open scoped Classical in
theorem altS_apply (o : NatOrdinal.{0}) :
    altS o = if Order.IsSuccPrelimit (NatOrdinal.val o) then 1 else -1 := rfl

open scoped Classical in
theorem altS_ne (o : NatOrdinal.{0}) : altS o ≠ 0 := by
  rw [altS_apply]; split_ifs <;> decide

theorem altS_ne_toSE (a : Surreal.{0}) : altS ≠ toSignExpansion a := by
  intro h
  have hs := small_toSignExpansion a
  rw [← h, small_iff_length_ne_top] at hs
  exact hs (length_eq_top.2 altS_ne)

theorem d_le (f : SignExpansion.{0}) (d : NatOrdinal.{0}) (h : ∀ j < d, f j = altS j) :
    (d : WithTop NatOrdinal) ≤ f.length := by
  by_contra hc
  push_neg at hc
  obtain ⟨l, hl⟩ := WithTop.ne_top_iff_exists.1 (hc.trans (WithTop.coe_lt_top d)).ne
  have hld : l < d := by rw [← hl] at hc; exact WithTop.coe_lt_coe.1 hc
  have := h l hld
  rw [SignExpansion.apply_of_length_le (le_of_eq hl.symm)] at this
  exact altS_ne l this.symm

noncomputable def X : Cut.{0} := sSup (rightSurreal '' {y : Surreal.{0} | toSignExpansion y < altS})

theorem X_left : X.left = {y : Surreal.{0} | toSignExpansion y < altS} := by
  rw [X, left_sSup]
  ext y
  simp only [Set.mem_iUnion, Set.biUnion_image, left_rightSurreal, Set.mem_Iic, Set.mem_setOf_eq,
    exists_prop]
  constructor
  · rintro ⟨a, ha, hya⟩; exact (toSignExpansion.monotone hya).trans_lt ha
  · intro h; exact ⟨y, h, le_rfl⟩

theorem exists_trunc (n : NatOrdinal.{0}) : ∃ r : Surreal.{0}, toSignExpansion r = altS ↾ (n : WithTop _) := by
  have : altS ↾ (n : WithTop NatOrdinal) ∈ Set.range toSignExpansion.{0} := by
    rw [range_toSignExpansion]; exact small_trunc _ _
  exact this

-- the first difference of altS with any surreal's expansion lies below its birthday
theorem diff_le {a : Surreal.{0}} {d : NatOrdinal.{0}}
    (hd : ∀ j < d, toSignExpansion a j = altS j) : d ≤ a.birthday := by
  have := d_le (toSignExpansion a) d hd
  rw [length_toSignExpansion] at this
  exact WithTop.coe_le_coe.1 this

theorem notSmallX : ¬ X.Small := by
  suffices ∀ y : Cut.{0}, y.Small → y ≠ X from fun h => this X h rfl
  intro y hy
  cases hy with
  | infLeft s =>
    intro e
    have hR : ∀ r, r ∈ X.right → ∃ a ∈ s, a ≤ r := by
      intro r hr; rw [← e, right_sInf] at hr; simpa using hr
    have hs : ∀ a ∈ s, altS < toSignExpansion a := by
      intro a ha
      have : a ∈ X.right := by rw [← e, right_sInf]; simp; exact ⟨a, ha, le_rfl⟩
      rw [← notMem_left_iff, X_left] at this
      simp only [Set.mem_setOf_eq, not_lt] at this
      exact lt_of_le_of_ne this (altS_ne_toSE a)
    obtain ⟨B, hB⟩ := NatOrdinal.bddAbove_of_small (Surreal.birthday '' s)
    let n : NatOrdinal.{0} := NatOrdinal.of (NatOrdinal.val B + 1)
    have hBn : B < n := show NatOrdinal.val B < NatOrdinal.val B + 1 from lt_add_one _
    have hn : altS n = -1 := by
      rw [altS_apply, if_neg]; exact Order.not_isSuccPrelimit_add_one _
    obtain ⟨r, hr⟩ := exists_trunc n
    have hrR : r ∈ X.right := by
      rw [← notMem_left_iff, X_left]
      simp only [Set.mem_setOf_eq, not_lt, hr]
      refine le_of_lt ?_
      rw [SignExpansion.lt_iff_toLex]
      refine ⟨n, fun j hj => ?_, ?_⟩
      · show altS j = (altS ↾ (n : WithTop _)) j
        exact (trunc_apply_of_coe_lt (WithTop.coe_lt_coe.2 hj)).symm
      · show altS n < (altS ↾ (n : WithTop _)) n
        rw [trunc_apply_of_le_coe le_rfl, hn]; decide
    obtain ⟨a, ha, har⟩ := hR r hrR
    have : r < a := by
      rw [← toSignExpansion.lt_iff_lt, hr]
      obtain ⟨d, hd1, hd2⟩ := SignExpansion.lt_iff_toLex.1 (hs a ha)
      have hdn : d < n := ((diff_le (fun j hj => (hd1 j hj).symm)).trans (hB ⟨a, ha, rfl⟩)).trans_lt hBn
      rw [SignExpansion.lt_iff_toLex]
      refine ⟨d, fun j hj => ?_, ?_⟩
      · show (altS ↾ (n : WithTop _)) j = toSignExpansion a j
        rw [trunc_apply_of_coe_lt (WithTop.coe_lt_coe.2 (hj.trans hdn))]; exact hd1 j hj
      · show (altS ↾ (n : WithTop _)) d < toSignExpansion a d
        rw [trunc_apply_of_coe_lt (WithTop.coe_lt_coe.2 hdn)]; exact hd2
    exact (har.trans_lt this).false
  | supRight s =>
    intro e
    have hL : ∀ r, r ∈ X.left → ∃ a ∈ s, r ≤ a := by
      intro r hr; rw [← e, left_sSup] at hr; simpa using hr
    have hs : ∀ a ∈ s, toSignExpansion a < altS := by
      intro a ha
      have : a ∈ X.left := by rw [← e, left_sSup]; simp; exact ⟨a, ha, le_rfl⟩
      rw [X_left] at this
      exact this
    obtain ⟨B, hB⟩ := NatOrdinal.bddAbove_of_small (Surreal.birthday '' s)
    let n : NatOrdinal.{0} := NatOrdinal.of (NatOrdinal.val B + Ordinal.omega0)
    have hBn : B < n := show NatOrdinal.val B < NatOrdinal.val B + Ordinal.omega0 from
      lt_add_of_pos_right _ Ordinal.omega0_pos
    have hn : altS n = 1 := by
      rw [altS_apply, if_pos]
      exact (Ordinal.isSuccLimit_add _ Ordinal.isSuccLimit_omega0).isSuccPrelimit
    obtain ⟨r, hr⟩ := exists_trunc n
    have hrL : r ∈ X.left := by
      rw [X_left]
      simp only [Set.mem_setOf_eq, hr]
      rw [SignExpansion.lt_iff_toLex]
      refine ⟨n, fun j hj => ?_, ?_⟩
      · show (altS ↾ (n : WithTop _)) j = altS j
        exact (trunc_apply_of_coe_lt (WithTop.coe_lt_coe.2 hj))
      · show (altS ↾ (n : WithTop _)) n < altS n
        rw [trunc_apply_of_le_coe le_rfl, hn]; decide
    obtain ⟨a, ha, hra⟩ := hL r hrL
    have : a < r := by
      rw [← toSignExpansion.lt_iff_lt, hr]
      obtain ⟨d, hd1, hd2⟩ := SignExpansion.lt_iff_toLex.1 (hs a ha)
      have hdn : d < n := ((diff_le (fun j hj => hd1 j hj)).trans (hB ⟨a, ha, rfl⟩)).trans_lt hBn
      rw [SignExpansion.lt_iff_toLex]
      refine ⟨d, fun j hj => ?_, ?_⟩
      · show toSignExpansion a j = (altS ↾ (n : WithTop _)) j
        rw [trunc_apply_of_coe_lt (WithTop.coe_lt_coe.2 (hj.trans hdn))]; exact hd1 j hj
      · show toSignExpansion a d < (altS ↾ (n : WithTop _)) d
        rw [trunc_apply_of_coe_lt (WithTop.coe_lt_coe.2 hdn)]; exact hd2
    exact (hra.trans_lt this).false

end W2c4

open Set Surreal.Cut W2c4

-- `Surreal.Cut.Small.birthday_lt_top` idx 1: necessary (x = a non-small cut: the gap of the On-length alternating sign sequence)
theorem c4_126 : ¬ drop0% Surreal.Cut.Small.birthday_lt_top 1 := fun h =>
  notSmallX (small_iff_birthday.2 (h X))
-- `Surreal.Cut.Numeric.small` idx 1: necessary (x = a non-small cut: the gap of the On-length alternating sign sequence)
theorem c4_127 : ¬ drop0% Surreal.Cut.Numeric.small 1 := fun h => notSmallX (h X)
-- `Surreal.Cut.Small.neg` idx 1: necessary (x = -X for the non-small cut X)
theorem c4_128 : ¬ drop0% Surreal.Cut.Small.neg 1 := fun h => notSmallX (by simpa using h (-X))
-- `Surreal.Cut.Small.iSup` idx 1: necessary (ι = left set of the non-small cut X (universe 1), f = rightSurreal: the supremum is X)
theorem c4_129 : ¬ dropU% Surreal.Cut.Small.iSup 1 [0, 1] := fun h => by
  have := @h X.left (fun i => rightSurreal i.1) (fun _ => inferInstance)
  rw [← sSup_image', sSup_rightSurreal_left] at this
  exact notSmallX this
-- `Surreal.Cut.Small.iSup` idx 3: necessary (ι = Unit, f = the non-small cut X)
theorem c4_130 : ¬ drop0% Surreal.Cut.Small.iSup 3 := fun h =>
  notSmallX (by simpa using @h Unit _ (fun _ => X))
-- `Surreal.Cut.Small.iInf` idx 1: necessary (ι = right set of the non-small cut X (universe 1), f = leftSurreal: the infimum is X)
theorem c4_131 : ¬ dropU% Surreal.Cut.Small.iInf 1 [0, 1] := fun h => by
  have := @h X.right (fun i => leftSurreal i.1) (fun _ => inferInstance)
  rw [← sInf_image', sInf_leftSurreal_right] at this
  exact notSmallX this
-- `Surreal.Cut.Small.iInf` idx 3: necessary (ι = Unit, f = the non-small cut X)
theorem c4_132 : ¬ drop0% Surreal.Cut.Small.iInf 3 := fun h =>
  notSmallX (by simpa using @h Unit _ (fun _ => X))
-- `Surreal.Cut.Small.sSup` idx 1: necessary (s = rightSurreal of the left set of the non-small cut X)
theorem c4_133 : ¬ drop0% Surreal.Cut.Small.sSup 1 := fun h => by
  have := @h (rightSurreal '' X.left) (by rintro _ ⟨a, _, rfl⟩; infer_instance)
  rw [sSup_rightSurreal_left] at this
  exact notSmallX this
-- `Surreal.Cut.Small.sSup` idx 2: necessary (s = {X}, X a non-small cut)
theorem c4_134 : ¬ drop0% Surreal.Cut.Small.sSup 2 := fun h =>
  notSmallX (by simpa using @h {X} (small_single X))
-- `Surreal.Cut.Small.sInf` idx 1: necessary (s = leftSurreal of the right set of the non-small cut X)
theorem c4_135 : ¬ drop0% Surreal.Cut.Small.sInf 1 := fun h => by
  have := @h (leftSurreal '' X.right) (by rintro _ ⟨a, _, rfl⟩; infer_instance)
  rw [sInf_leftSurreal_right] at this
  exact notSmallX this
-- `Surreal.Cut.Small.sInf` idx 2: necessary (s = {X}, X a non-small cut)
theorem c4_136 : ¬ drop0% Surreal.Cut.Small.sInf 2 := fun h =>
  notSmallX (by simpa using @h {X} (small_single X))
-- `Surreal.Cut.Small.vadd` idx 2: necessary (x = 0, y = the non-small cut X)
theorem c4_137 : ¬ drop0% Surreal.Cut.Small.vadd 2 := fun h => notSmallX (by simpa using h 0 X)
-- `Surreal.Cut.exists_of_player_eq_left` idx 1: necessary (x = the non-small cut X)
theorem c4_138 : ¬ indep0% Surreal.Cut.exists_of_player_eq_left 1 := fun h => notSmallX (@h X)
-- `Surreal.Cut.exists_of_player_eq_right` idx 1: necessary (x = the non-small cut X)
theorem c4_139 : ¬ indep0% Surreal.Cut.exists_of_player_eq_right 1 := fun h => notSmallX (@h X)
-- `Surreal.Cut.player_neg` idx 1: necessary (x = the non-small cut X)
theorem c4_140 : ¬ indep0% Surreal.Cut.player_neg 1 := fun h => notSmallX (h X)
-- `Surreal.Cut.player_vadd` idx 2: necessary (y = the non-small cut X)
theorem c4_141 : ¬ indep0% Surreal.Cut.player_vadd 2 := fun h => notSmallX (h 0 X)
