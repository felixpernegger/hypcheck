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

set_option linter.unusedVariables false

namespace W1c1
open IGame

-- helper: a game graph on Option Type whose q-moves from none are all of Type (not Small.{0})
def gg (q : Player) : GameGraph.{1} (Option Type) :=
  ⟨fun p a => match a with | none => if p = q then Set.range some else ∅ | some _ => ∅⟩

theorem gg_smallR : ∀ a, Small.{0} ↑((gg .left).moves .right a) := by
  intro a; cases a <;> simp [gg] <;> exact small_empty

theorem gg_smallL : ∀ a, Small.{0} ↑((gg .right).moves .left a) := by
  intro a; cases a <;> simp [gg] <;> exact small_empty

theorem gg_not_small (q : Player) : ¬ ∀ a, Small.{0} ↑((gg q).moves q a) := fun h => by
  have h1 := h none
  simp only [gg, ite_true] at h1
  exact not_small_type.{0, 0} (small_of_injective (f := fun t : Type => (⟨some t, t, rfl⟩ : Set.range some))
    (fun a b e => Option.some_injective _ (congrArg Subtype.val e)))

theorem gg_wf (q : Player) : (gg q).WellFounded := ⟨by
  refine Subrelation.wf (r := InvImage (· < ·) (fun a : Option Type => cond a.isNone 1 0)) ?_
    (InvImage.wf _ Nat.lt_wfRel.wf)
  rintro a b ⟨p, hp⟩
  cases b with
  | some _ => simp [gg] at hp
  | none =>
    cases a with
    | none => simp [gg] at hp
    | some _ => simp [InvImage]⟩

-- helper: the graph on Unit with every move (not well-founded)
def gU : GameGraph.{0} Unit := ⟨fun _ _ => Set.univ⟩

theorem noLoop {α : Sort*} {r : α → α → Prop} (hr : ∀ x, r x x) (wf : WellFounded r) (a : α) : False := by
  induction wf.apply a with
  | intro x _ ih => exact ih x (hr x)

theorem gU_not_wf : ¬ gU.WellFounded := fun h => noLoop (fun _ => ⟨.left, trivial⟩) h.wf ()

-- helper: the graph on Unit without moves (well-founded)
def gE : GameGraph.{0} Unit := ⟨fun _ _ => ∅⟩

theorem gE_wf : gE.WellFounded := ⟨⟨fun a => ⟨a, fun _ ⟨_, h⟩ => h.elim⟩⟩⟩

-- helper: the graph on Bool with the single left move true → false (toIGame true = 1)
def gB : GameGraph.{0} Bool := ⟨fun p a => match p, a with | .left, true => {false} | _, _ => ∅⟩

theorem gB_wf : gB.WellFounded := ⟨by
  refine Subrelation.wf (r := InvImage (· < ·) (fun a : Bool => cond a 1 0)) ?_
    (InvImage.wf _ Nat.lt_wfRel.wf)
  rintro a b ⟨p, hp⟩
  cases p <;> cases a <;> cases b <;> simp [gB, InvImage] at hp ⊢⟩

-- `GameGraph.moves_toLGame`
theorem w_1 : ¬ ∀ {α : Type 1} (c : GameGraph.{1} α) (p : Player)
    [Hl : ∀ a, Small.{0} ↑(c.moves .left a)] (a a' : α), Small.{0} ↑(c.moves .right a') := fun h =>
  gg_not_small .right (@h _ (gg .right) .left gg_smallL none)

-- `GameGraph.toLGame_def'`
theorem w_2 : ¬ ∀ {α : Type 1} {c : GameGraph.{1} α}
    [Hr : ∀ a, Small.{0} ↑(c.moves .right a)] (a a' : α), Small.{0} ↑(c.moves .left a') := fun h =>
  gg_not_small .left (@h _ (gg .left) gg_smallR none)

-- `GameGraph.WellFounded.wf`
theorem w_9 : ¬ drop0% GameGraph.WellFounded.wf 2 := fun h => gU_not_wf ⟨h gU⟩

-- `GameGraph.WellFounded.of_subrelation`
theorem w_10 : ¬ drop0% GameGraph.WellFounded.of_subrelation 3 := fun h =>
  gU_not_wf (@h _ gU (fun _ _ => True) (fun _ _ _ _ => trivial))

-- `GameGraph.toIGame_def'`
theorem w_13 : ¬ ∀ {α : Type 1} {c : GameGraph.{1} α}
    [Hr : ∀ a, Small.{0} ↑(c.moves .right a)] [c.WellFounded] (a a' : α), Small.{0} ↑(c.moves .left a') :=
  fun h => gg_not_small .left (@h _ (gg .left) gg_smallR (gg_wf _) none)

-- `GameGraph.toIGame_def'`
theorem w_15 : ¬ indep0% GameGraph.toIGame_def' 4 := fun h =>
  gU_not_wf (@h _ gU (fun _ => inferInstance) (fun _ => inferInstance) ())

-- `GameGraph.toLGame_def'`
theorem w_3 : ¬ ∀ {α : Type 1} {c : GameGraph.{1} α}
    [Hl : ∀ a, Small.{0} ↑(c.moves .left a)] (a a' : α), Small.{0} ↑(c.moves .right a') := fun h =>
  gg_not_small .right (@h _ (gg .right) gg_smallL none)

-- `GameGraph.toLGame_def`
theorem w_4 : ¬ ∀ {α : Type 1} {c : GameGraph.{1} α}
    [Hr : ∀ a, Small.{0} ↑(c.moves .right a)] (a a' : α), Small.{0} ↑(c.moves .left a') := fun h =>
  gg_not_small .left (@h _ (gg .left) gg_smallR none)

-- `GameGraph.toLGame_def`
theorem w_5 : ¬ ∀ {α : Type 1} {c : GameGraph.{1} α}
    [Hl : ∀ a, Small.{0} ↑(c.moves .left a)] (a a' : α), Small.{0} ↑(c.moves .right a') := fun h =>
  gg_not_small .right (@h _ (gg .right) gg_smallL none)

-- `GameGraph.mem_moves_toLGame_of_mem`
theorem w_6 : ¬ ∀ {α : Type 1} {c : GameGraph.{1} α} {p : Player}
    [Hr : ∀ a, Small.{0} ↑(c.moves .right a)] {a b : α}, b ∈ c.moves p a →
      ∀ a' : α, Small.{0} ↑(c.moves .left a') := fun h =>
  gg_not_small .left (@h _ (gg .left) .left gg_smallR none (some Unit) ⟨Unit, rfl⟩)

-- `GameGraph.mem_moves_toLGame_of_mem`
theorem w_7 : ¬ ∀ {α : Type 1} {c : GameGraph.{1} α} {p : Player}
    [Hl : ∀ a, Small.{0} ↑(c.moves .left a)] {a b : α}, b ∈ c.moves p a →
      ∀ a' : α, Small.{0} ↑(c.moves .right a') := fun h =>
  gg_not_small .right (@h _ (gg .right) .right gg_smallL none (some Unit) ⟨Unit, rfl⟩)

-- `GameGraph.neg_toLGame`
theorem w_8 : ¬ drop0% GameGraph.neg_toLGame 4 := fun h => by
  have e := congrArg (LGame.moves .right)
    (@h Bool gB (fun _ => inferInstance) (fun _ => inferInstance) true)
  simp [gB] at e

-- `GameGraph.WellFounded.of_subrelation`
theorem w_11 : ¬ drop0% GameGraph.WellFounded.of_subrelation 4 := fun h =>
  gU_not_wf (@h _ gU (fun _ _ => False) ⟨fun a => ⟨a, fun _ h => h.elim⟩⟩)

-- `GameGraph.moveRecOn_eq`
theorem w_12 : ¬ indep0% GameGraph.moveRecOn_eq 2 := fun h =>
  gU_not_wf (@h _ gU (fun _ => True) () (fun _ _ => trivial))

-- `GameGraph.toIGame_def'`
theorem w_14 : ¬ ∀ {α : Type 1} {c : GameGraph.{1} α}
    [Hl : ∀ a, Small.{0} ↑(c.moves .left a)] [c.WellFounded] (a a' : α), Small.{0} ↑(c.moves .right a') :=
  fun h => gg_not_small .right (@h _ (gg .right) gg_smallL (gg_wf _) none)

-- `GameGraph.toIGame_def`
theorem w_16 : ¬ ∀ {α : Type 1} {c : GameGraph.{1} α}
    [Hr : ∀ a, Small.{0} ↑(c.moves .right a)] [c.WellFounded] (a a' : α), Small.{0} ↑(c.moves .left a') :=
  fun h => gg_not_small .left (@h _ (gg .left) gg_smallR (gg_wf _) none)

-- `GameGraph.toIGame_def`
theorem w_17 : ¬ ∀ {α : Type 1} {c : GameGraph.{1} α}
    [Hl : ∀ a, Small.{0} ↑(c.moves .left a)] [c.WellFounded] (a a' : α), Small.{0} ↑(c.moves .right a') :=
  fun h => gg_not_small .right (@h _ (gg .right) gg_smallL (gg_wf _) none)

-- `GameGraph.toIGame_def`
theorem w_18 : ¬ indep0% GameGraph.toIGame_def 4 := fun h =>
  gU_not_wf (@h _ gU (fun _ => inferInstance) (fun _ => inferInstance) ())

-- `GameGraph.moves_toIGame`
theorem w_19 : ¬ ∀ {α : Type 1} (c : GameGraph.{1} α) (p : Player)
    [Hr : ∀ a, Small.{0} ↑(c.moves .right a)] [c.WellFounded] (a a' : α), Small.{0} ↑(c.moves .left a') :=
  fun h => gg_not_small .left (@h _ (gg .left) .left gg_smallR (gg_wf _) none)

-- `GameGraph.moves_toIGame`
theorem w_20 : ¬ ∀ {α : Type 1} (c : GameGraph.{1} α) (p : Player)
    [Hl : ∀ a, Small.{0} ↑(c.moves .left a)] [c.WellFounded] (a a' : α), Small.{0} ↑(c.moves .right a') :=
  fun h => gg_not_small .right (@h _ (gg .right) .left gg_smallL (gg_wf _) none)

-- `GameGraph.moves_toIGame`
theorem w_21 : ¬ indep0% GameGraph.moves_toIGame 5 := fun h =>
  gU_not_wf (@h _ gU .left (fun _ => inferInstance) (fun _ => inferInstance) ())

-- `GameGraph.mem_moves_toIGame_of_mem`
theorem w_22 : ¬ ∀ {α : Type 1} {c : GameGraph.{1} α} {p : Player}
    [Hr : ∀ a, Small.{0} ↑(c.moves .right a)] [c.WellFounded] {a b : α}, b ∈ c.moves p a →
      ∀ a' : α, Small.{0} ↑(c.moves .left a') := fun h =>
  gg_not_small .left (@h _ (gg .left) .left gg_smallR (gg_wf _) none (some Unit) ⟨Unit, rfl⟩)

-- `GameGraph.mem_moves_toIGame_of_mem`
theorem w_23 : ¬ ∀ {α : Type 1} {c : GameGraph.{1} α} {p : Player}
    [Hl : ∀ a, Small.{0} ↑(c.moves .left a)] [c.WellFounded] {a b : α}, b ∈ c.moves p a →
      ∀ a' : α, Small.{0} ↑(c.moves .right a') := fun h =>
  gg_not_small .right (@h _ (gg .right) .right gg_smallL (gg_wf _) none (some Unit) ⟨Unit, rfl⟩)

-- `GameGraph.mem_moves_toIGame_of_mem`
theorem w_24 : ¬ indep0% GameGraph.mem_moves_toIGame_of_mem 5 := fun h =>
  gU_not_wf (@h _ gU .left (fun _ => inferInstance) (fun _ => inferInstance) () () trivial)

-- `GameGraph.mem_moves_toIGame_of_mem`
theorem w_25 : ¬ drop0% GameGraph.mem_moves_toIGame_of_mem 8 := fun h =>
  self_notMem_moves _ _ (@h _ gE .left (fun _ => inferInstance) (fun _ => inferInstance) gE_wf () ())

-- `GameGraph.toLGame_toIGame`
theorem w_26 : ¬ ∀ {α : Type 1} (c : GameGraph.{1} α)
    [Hr : ∀ a, Small.{0} ↑(c.moves .right a)] [c.WellFounded] (a a' : α), Small.{0} ↑(c.moves .left a') :=
  fun h => gg_not_small .left (@h _ (gg .left) gg_smallR (gg_wf _) none)

-- `GameGraph.toLGame_toIGame`
theorem w_27 : ¬ ∀ {α : Type 1} (c : GameGraph.{1} α)
    [Hl : ∀ a, Small.{0} ↑(c.moves .left a)] [c.WellFounded] (a a' : α), Small.{0} ↑(c.moves .right a') :=
  fun h => gg_not_small .right (@h _ (gg .right) gg_smallL (gg_wf _) none)

-- `GameGraph.toLGame_toIGame`
theorem w_28 : ¬ indep0% GameGraph.toLGame_toIGame 4 := fun h =>
  gU_not_wf (@h _ gU (fun _ => inferInstance) (fun _ => inferInstance) ())

-- `GameGraph.neg_toIGame`
theorem w_29 : ¬ indep0% GameGraph.neg_toIGame 4 := fun h =>
  gU_not_wf (@h _ gU (fun _ => inferInstance) (fun _ => inferInstance) rfl ())

-- `GameGraph.neg_toIGame`
theorem w_30 : ¬ drop0% GameGraph.neg_toIGame 5 := fun h => by
  have e := congrArg (IGame.moves .left)
    (@h Bool gB (fun _ => inferInstance) (fun _ => inferInstance) gB_wf true)
  simp [gB] at e

-- `GameGraph.impartial_toIGame`
theorem w_31 : ¬ indep0% GameGraph.impartial_toIGame 4 := fun h =>
  gU_not_wf (@h _ gU (fun _ => inferInstance) (fun _ => inferInstance) rfl ())

theorem gB_false : @GameGraph.toIGame _ gB (fun _ => inferInstance) (fun _ => inferInstance) gB_wf false = 0 := by
  ext p; cases p <;> simp [gB]

theorem gB_true : @GameGraph.toIGame _ gB (fun _ => inferInstance) (fun _ => inferInstance) gB_wf true = 1 := by
  have h1 : gB.moves .left true = {false} := rfl
  have h2 : gB.moves .right true = ∅ := rfl
  ext p; cases p <;> simp [h1, h2, gB_false]

-- `GameGraph.impartial_toIGame`
theorem w_32 : ¬ drop0% GameGraph.impartial_toIGame 5 := fun h => by
  have := @h Bool gB (fun _ => inferInstance) (fun _ => inferInstance) gB_wf true
  rw [gB_true] at this
  exact absurd (impartial_def.1 this).1 (by game_cmp)

end W1c1

namespace W1c1
open IGame

-- helper: the universe of IGame is not small (from Probe1)
theorem notSmallIGame.{u} : ¬ Small.{u} (Set.univ : Set IGame.{u}) := by
  rw [small_univ_iff]; intro h
  exact not_small_ordinal.{u} (small_of_injective (f := fun o : NatOrdinal.{u} => NatOrdinal.toIGame o)
    NatOrdinal.toIGame.injective)

-- helper: move-set families with one side all of IGame
def stL : Player → Set IGame.{0} := fun p => match p with | .left => Set.univ | .right => ∅
def stR : Player → Set IGame.{0} := fun p => match p with | .left => ∅ | .right => Set.univ

theorem se : Small.{0} ↑(∅ : Set IGame.{0}) := small_empty

theorem s01 : Subposition (0 : IGame) 1 := .of_mem_moves (p := .left) (by simp)

theorem one_ne_zero' : (1 : IGame) ≠ 0 := fun e => by
  have := congrArg (IGame.moves .left) e; simp at this

theorem not_subp_zero (x : IGame) : ¬ Subposition x 0 := fun h => by
  rw [subposition_iff_exists] at h; simp at h

theorem not_wsubp_one_zero : ¬ WSubposition (1 : IGame) 0 := fun h =>
  h.elim one_ne_zero' (not_subp_zero 1)

-- `IGame.moves_ofSets`
theorem w_33 : ¬ indep0% IGame.moves_ofSets 2 := fun h => notSmallIGame (@h .left stL se)
-- `IGame.moves_ofSets`
theorem w_34 : ¬ indep0% IGame.moves_ofSets 3 := fun h => notSmallIGame (@h .left stR se)
-- `IGame.moves_left_ofSets`
theorem w_35 : ¬ indep0% IGame.moves_left_ofSets 2 := fun h => notSmallIGame (@h Set.univ ∅ se)
-- `IGame.moves_left_ofSets`
theorem w_36 : ¬ indep0% IGame.moves_left_ofSets 3 := fun h => notSmallIGame (@h ∅ Set.univ se)
-- `IGame.moves_right_ofSets`
theorem w_37 : ¬ indep0% IGame.moves_right_ofSets 2 := fun h => notSmallIGame (@h Set.univ ∅ se)
-- `IGame.moves_right_ofSets`
theorem w_38 : ¬ indep0% IGame.moves_right_ofSets 3 := fun h => notSmallIGame (@h ∅ Set.univ se)
-- `IGame.ofSets_inj'`
theorem w_39 : ¬ indep0% IGame.ofSets_inj' 2 := fun h => notSmallIGame (@h stL (fun _ => ∅) se se se)
-- `IGame.ofSets_inj'`
theorem w_40 : ¬ indep0% IGame.ofSets_inj' 3 := fun h => notSmallIGame (@h stR (fun _ => ∅) se se se)
-- `IGame.ofSets_inj'`
theorem w_41 : ¬ indep0% IGame.ofSets_inj' 4 := fun h => notSmallIGame (@h (fun _ => ∅) stL se se se)
-- `IGame.ofSets_inj'`
theorem w_42 : ¬ indep0% IGame.ofSets_inj' 5 := fun h => notSmallIGame (@h (fun _ => ∅) stR se se se)
-- `IGame.ofSets_inj`
theorem w_43 : ¬ indep0% IGame.ofSets_inj 4 := fun h => notSmallIGame (@h Set.univ ∅ ∅ ∅ se se se)
-- `IGame.ofSets_inj`
theorem w_44 : ¬ indep0% IGame.ofSets_inj 5 := fun h => notSmallIGame (@h ∅ Set.univ ∅ ∅ se se se)
-- `IGame.ofSets_inj`
theorem w_45 : ¬ indep0% IGame.ofSets_inj 6 := fun h => notSmallIGame (@h ∅ ∅ Set.univ ∅ se se se)
-- `IGame.ofSets_inj`
theorem w_46 : ¬ indep0% IGame.ofSets_inj 7 := fun h => notSmallIGame (@h ∅ ∅ ∅ Set.univ se se se)

-- `IGame.Subposition.of_mem_moves`
theorem w_47 : ¬ drop0% IGame.Subposition.of_mem_moves 3 := fun h => Subposition.irrefl 0 (@h .left 0 0)
-- `IGame.Subposition.trans`
theorem w_48 : ¬ drop0% IGame.Subposition.trans 4 := fun h => Subposition.irrefl 0 (@h 0 1 0 s01)
-- `IGame.wsubposition_of_eq`
theorem w_49 : ¬ drop0% IGame.wsubposition_of_eq 2 := fun h => not_wsubp_one_zero (@h 1 0)
-- `IGame.wsubposition_of_subposition`
theorem w_50 : ¬ drop0% IGame.wsubposition_of_subposition 2 := fun h => not_wsubp_one_zero (@h 1 0)
-- `IGame.Subposition.wsubposition`
theorem w_51 : ¬ drop0% IGame.Subposition.wsubposition 2 := fun h => not_wsubp_one_zero (@h 1 0)
-- `IGame.subposition_of_wsubposition_of_subposition`
theorem w_52 : ¬ drop0% IGame.subposition_of_wsubposition_of_subposition 3 := fun h =>
  Subposition.irrefl 1 (@h 1 0 1 s01)
-- `IGame.subposition_of_wsubposition_of_subposition`
theorem w_53 : ¬ drop0% IGame.subposition_of_wsubposition_of_subposition 4 := fun h =>
  Subposition.irrefl 0 (@h 0 0 0 .rfl)
-- `IGame.subposition_of_subposition_of_wsubposition`
theorem w_54 : ¬ drop0% IGame.subposition_of_subposition_of_wsubposition 4 := fun h =>
  Subposition.irrefl 0 (@h 0 1 0 s01)
-- `IGame.WSubposition.trans_subposition`
theorem w_55 : ¬ drop0% IGame.WSubposition.trans_subposition 3 := fun h =>
  Subposition.irrefl 1 (@h 1 0 1 s01)
-- `IGame.WSubposition.trans_subposition`
theorem w_56 : ¬ drop0% IGame.WSubposition.trans_subposition 4 := fun h =>
  Subposition.irrefl 0 (@h 0 0 0 .rfl)
-- `IGame.Subposition.trans_wsubposition'`
theorem w_57 : ¬ drop0% IGame.Subposition.trans_wsubposition' 3 := fun h =>
  Subposition.irrefl 1 (@h 1 0 1 s01)
-- `IGame.Subposition.trans_wsubposition'`
theorem w_58 : ¬ drop0% IGame.Subposition.trans_wsubposition' 4 := fun h =>
  Subposition.irrefl 0 (@h 0 0 0 .rfl)
-- `IGame.Subposition.trans_wsubposition`
theorem w_59 : ¬ drop0% IGame.Subposition.trans_wsubposition 4 := fun h =>
  Subposition.irrefl 0 (@h 0 1 0 s01)
-- `IGame.WSubposition.trans_subposition'`
theorem w_60 : ¬ drop0% IGame.WSubposition.trans_subposition' 4 := fun h =>
  Subposition.irrefl 0 (@h 0 1 0 s01)
-- `IGame.wsubposition_trans`
theorem w_61 : ¬ drop0% IGame.wsubposition_trans 4 := fun h => not_wsubp_one_zero (@h 1 1 0 .rfl)
-- `IGame.WSubposition.trans`
theorem w_62 : ¬ drop0% IGame.WSubposition.trans 4 := fun h => not_wsubp_one_zero (@h 1 1 0 .rfl)
-- `IGame.not_subposition_of_wsubposition`
theorem w_63 : ¬ drop0% IGame.not_subposition_of_wsubposition 2 := fun h => @h 1 0 s01
-- `IGame.WSubposition.not_subposition`
theorem w_64 : ¬ drop0% IGame.WSubposition.not_subposition 2 := fun h => @h 1 0 s01
-- `IGame.wsubposition_antisymm`
theorem w_65 : ¬ drop0% IGame.wsubposition_antisymm 2 := fun h => one_ne_zero' (@h 1 0 s01.wsubposition)
-- `IGame.wsubposition_antisymm`
theorem w_66 : ¬ drop0% IGame.wsubposition_antisymm 3 := fun h => one_ne_zero' (@h 0 1 s01.wsubposition).symm
-- `IGame.WSubposition.antisymm`
theorem w_67 : ¬ drop0% IGame.WSubposition.antisymm 2 := fun h => one_ne_zero' (@h 1 0 s01.wsubposition)
-- `IGame.WSubposition.antisymm`
theorem w_68 : ¬ drop0% IGame.WSubposition.antisymm 3 := fun h => one_ne_zero' (@h 0 1 s01.wsubposition).symm
-- `IGame.subposition_of_wsubposition_of_ne`
theorem w_69 : ¬ drop0% IGame.subposition_of_wsubposition_of_ne 3 := fun h =>
  Subposition.irrefl 0 (@h 0 0 .rfl)

theorem not_subp_one_neg_one : ¬ Subposition (1 : IGame) (-1) := fun h => by
  rw [subposition_iff_exists] at h
  obtain ⟨p, z, hz, hw⟩ := h
  cases p <;> simp at hz
  subst hz
  exact not_wsubp_one_zero hw

theorem not_wsubp_neg_one_one : ¬ WSubposition (-1 : IGame) 1 := fun h => by
  rcases h with e | h
  · have := congrArg (IGame.moves .left) e; simp at this
  · rw [subposition_iff_exists] at h
    obtain ⟨p, z, hz, hw⟩ := h
    cases p <;> simp at hz
    subst hz
    rcases hw with e | h
    · have := congrArg (IGame.moves .right) e; simp at this
    · exact not_subp_zero _ h

-- `IGame.subposition_of_wsubposition_not_wsubposition`
theorem w_70 : ¬ drop0% IGame.subposition_of_wsubposition_not_wsubposition 2 := fun h =>
  not_subp_one_neg_one (@h 1 (-1) not_wsubp_neg_one_one)
-- `IGame.subposition_of_wsubposition_not_wsubposition`
theorem w_71 : ¬ drop0% IGame.subposition_of_wsubposition_not_wsubposition 3 := fun h =>
  Subposition.irrefl 0 (@h 0 0 .rfl)
-- `IGame.WSubposition.of_mem_moves`
theorem w_72 : ¬ drop0% IGame.WSubposition.of_mem_moves 3 := fun h => not_wsubp_one_zero (@h .left 1 0)

-- `IGame.ofSetsRecOn_ofSets`
theorem w_73 : ¬ indep0% IGame.ofSetsRecOn_ofSets 3 := fun h =>
  notSmallIGame (@h (fun _ => True) Set.univ ∅ se (fun _ _ _ _ _ _ => trivial))
-- `IGame.ofSetsRecOn_ofSets`
theorem w_74 : ¬ indep0% IGame.ofSetsRecOn_ofSets 4 := fun h =>
  notSmallIGame (@h (fun _ => True) ∅ Set.univ se (fun _ _ _ _ _ _ => trivial))
-- `IGame.lf_right_of_le`
theorem w_75 : ¬ drop0% IGame.lf_right_of_le 3 := fun h => @h 0 (-1) 0 (by simp) le_rfl
-- `IGame.lf_of_right_le`
theorem w_76 : ¬ drop0% IGame.lf_of_right_le 3 := fun h => @h (-1) (-1) 0 (by simp) le_rfl
-- `_private.CombinatorialGames.Game.IGame.0.IGame.neg_ofSets''`
theorem w_77 : ¬ indep0% _private.CombinatorialGames.Game.IGame.«0».IGame.neg_ofSets'' 2 := fun h =>
  notSmallIGame (@h Set.univ ∅ se)
-- `_private.CombinatorialGames.Game.IGame.0.IGame.neg_ofSets''`
theorem w_78 : ¬ indep0% _private.CombinatorialGames.Game.IGame.«0».IGame.neg_ofSets'' 3 := fun h =>
  notSmallIGame (@h ∅ Set.univ se)
-- `IGame.neg_ofSets`
theorem w_79 : ¬ indep0% IGame.neg_ofSets 2 := fun h => notSmallIGame (@h Set.univ ∅ se)
-- `IGame.neg_ofSets`
theorem w_80 : ¬ indep0% IGame.neg_ofSets 3 := fun h => notSmallIGame (@h ∅ Set.univ se)
-- `IGame.neg_ofSets'`
theorem w_81 : ¬ indep0% IGame.neg_ofSets' 1 := fun h => notSmallIGame (@h stL se)
-- `IGame.neg_ofSets'`
theorem w_82 : ¬ indep0% IGame.neg_ofSets' 2 := fun h => notSmallIGame (@h stR se)
-- `IGame.neg_ofSets_const`
theorem w_83 : ¬ indep0% IGame.neg_ofSets_const 1 := fun h => notSmallIGame (h Set.univ)
-- `IGame.ofSets_add_ofSets`
theorem w_84 : ¬ indep0% IGame.ofSets_add_ofSets 4 := fun h => notSmallIGame (@h Set.univ ∅ ∅ ∅ se se se)
-- `IGame.ofSets_add_ofSets`
theorem w_85 : ¬ indep0% IGame.ofSets_add_ofSets 5 := fun h => notSmallIGame (@h ∅ Set.univ ∅ ∅ se se se)
-- `IGame.ofSets_add_ofSets`
theorem w_86 : ¬ indep0% IGame.ofSets_add_ofSets 6 := fun h => notSmallIGame (@h ∅ ∅ Set.univ ∅ se se se)
-- `IGame.ofSets_add_ofSets`
theorem w_87 : ¬ indep0% IGame.ofSets_add_ofSets 7 := fun h => notSmallIGame (@h ∅ ∅ ∅ Set.univ se se se)
-- `IGame.ofSets_add_ofSets'`
theorem w_88 : ¬ indep0% IGame.ofSets_add_ofSets' 3 := fun h => notSmallIGame (@h (fun _ => ∅) stL se se se)
-- `IGame.ofSets_add_ofSets'`
theorem w_89 : ¬ indep0% IGame.ofSets_add_ofSets' 4 := fun h => notSmallIGame (@h stR (fun _ => ∅) se se se)
-- `IGame.ofSets_add_ofSets'`
theorem w_90 : ¬ indep0% IGame.ofSets_add_ofSets' 5 := fun h => notSmallIGame (@h (fun _ => ∅) stR se se se)
-- `IGame.eq_intCast_of_mem_moves_left_intCast`
theorem w_91 : ¬ drop0% IGame.eq_intCast_of_mem_moves_left_intCast 2 := fun h => by
  obtain ⟨m, hm, e⟩ := @h 0 ((0 : ℤ) : IGame)
  rw [intCast_inj] at e; omega
-- `IGame.eq_intCast_of_mem_moves_right_intCast`
theorem w_92 : ¬ drop0% IGame.eq_intCast_of_mem_moves_right_intCast 2 := fun h => by
  obtain ⟨m, hm, e⟩ := @h 0 ((0 : ℤ) : IGame)
  rw [intCast_inj] at e; omega
-- `IGame.ofSets_mul_ofSets`
theorem w_93 : ¬ indep0% IGame.ofSets_mul_ofSets 4 := fun h => notSmallIGame (@h Set.univ ∅ ∅ ∅ se se se)
-- `IGame.ofSets_mul_ofSets`
theorem w_94 : ¬ indep0% IGame.ofSets_mul_ofSets 5 := fun h => notSmallIGame (@h ∅ Set.univ ∅ ∅ se se se)
-- `IGame.ofSets_mul_ofSets`
theorem w_95 : ¬ indep0% IGame.ofSets_mul_ofSets 6 := fun h => notSmallIGame (@h ∅ ∅ Set.univ ∅ se se se)
-- `IGame.ofSets_mul_ofSets`
theorem w_96 : ¬ indep0% IGame.ofSets_mul_ofSets 7 := fun h => notSmallIGame (@h ∅ ∅ ∅ Set.univ se se se)

end W1c1

namespace W1c1
open IGame

-- helper: if 0 < x and x has no positive option, every move of x⁻¹ is the left move 0
theorem invMoves_triv {x : IGame} (hx : 0 < x) (hno : ∀ p, ∀ y ∈ x.moves p, ¬ 0 < y) :
    ∀ p y, y ∈ x⁻¹.moves p → p = .left ∧ y = 0 :=
  invRec hx (P := fun p y _ => p = .left ∧ y = 0) ⟨rfl, rfl⟩
    (fun _ _ y hy hyx _ _ _ => absurd hy (hno _ y hyx))

theorem one_inv_moves : ∀ p y, y ∈ (1 : IGame)⁻¹.moves p → p = .left ∧ y = 0 :=
  invMoves_triv (by game_cmp) (fun p y hy => by cases p <;> simp at hy; subst hy; exact lt_irrefl 0)

theorem zero_mem_inv' : (0 : IGame) ∈ ((priv% _private.CombinatorialGames.Game.IGame.«0».IGame.inv') (0 : IGame)).moves .left := by
  rw [priv% _private.CombinatorialGames.Game.IGame.«0».IGame.inv'.eq_1, moves_left_ofSets]
  exact ⟨(priv% _private.CombinatorialGames.Game.IGame.«0».IGame.InvTy.zero) (lr := _), rfl⟩

-- `_private.CombinatorialGames.Game.IGame.0.IGame.inv_eq`
theorem w_97 : ¬ drop0% _private.CombinatorialGames.Game.IGame.«0».IGame.inv_eq 1 := fun h => by
  have e := congrArg (IGame.moves .left) (@h 0)
  rw [IGame.inv_zero, moves_left_ofSets] at e
  have hx := (Set.ext_iff.1 e _).2 ⟨(priv% _private.CombinatorialGames.Game.IGame.«0».IGame.InvTy.zero) (lr := _), rfl⟩
  simp at hx

-- `_private.CombinatorialGames.Game.IGame.0.IGame.inv_eq'`
theorem w_98 : ¬ drop0% _private.CombinatorialGames.Game.IGame.«0».IGame.inv_eq' 1 := fun h => by
  have e := congrArg (IGame.moves .left) (@h 0)
  rw [IGame.inv_zero, moves_ofSets] at e
  have hx := (Set.ext_iff.1 e _).2 ⟨(priv% _private.CombinatorialGames.Game.IGame.«0».IGame.InvTy.zero) (lr := _), rfl⟩
  simp at hx

-- `IGame.inv_of_equiv_zero`
theorem w_99 : ¬ drop0% IGame.inv_of_equiv_zero 1 := fun h => by
  have := zero_mem_moves_left_inv (x := 1) (by game_cmp)
  rw [h] at this; simp at this

-- `_private.CombinatorialGames.Game.IGame.0.IGame.invOption_eq`
theorem w_100 : ¬ drop0% _private.CombinatorialGames.Game.IGame.«0».IGame.invOption_eq 3 := fun h => by
  have e := congrArg (IGame.moves .left) (@h 0 0 0)
  have hm : _ ∈ (((1 : IGame) + (0 - 0) * 0) * _).moves .left := mulOption_mem_moves_mul (px := .left) (py := .left)
    (x := 1 + (0 - 0) * 0) (a := 0 + (0 - 0) * 0) (by simp) zero_mem_inv'
  rw [← e] at hm
  simp [invOption, IGame.div_eq_mul_inv] at hm

-- `IGame.invOption_mem_moves_inv`
theorem w_102 : ¬ drop0% IGame.invOption_mem_moves_inv 6 := fun h => by
  have := @h 1 0 0 .left .right (by game_cmp) (by simp) (zero_mem_moves_left_inv (by game_cmp))
  exact absurd (one_inv_moves _ _ this).1 (by decide)

-- `IGame.invOption_mem_moves_inv`
theorem w_103 : ¬ drop0% IGame.invOption_mem_moves_inv 7 := fun h => by
  have := @h 1 1 0 .left .right (by game_cmp) (by game_cmp) (zero_mem_moves_left_inv (by game_cmp))
  exact absurd (one_inv_moves _ _ this).1 (by decide)

theorem zero_mem_negone_inv : (0 : IGame) ∈ (-1 : IGame)⁻¹.moves .right := by
  rw [IGame.inv_neg, moves_neg]
  simpa using zero_mem_moves_left_inv (x := 1) (by game_cmp)

-- `_private.CombinatorialGames.Game.IGame.0.IGame.invRec'`
theorem w_105 : ¬ indep0% _private.CombinatorialGames.Game.IGame.«0».IGame.invRec' 1 := fun h =>
  absurd (@h (-1) (fun _ _ _ => True) .right 0 zero_mem_negone_inv) (by game_cmp)

-- `_private.CombinatorialGames.Game.IGame.0.IGame.invRec'`
theorem w_106 : ¬ drop0% _private.CombinatorialGames.Game.IGame.«0».IGame.invRec' 3 := fun h =>
  @h 1 (by game_cmp) (fun _ _ _ => False) (fun _ _ _ _ _ _ _ h => h) .left 0
    (zero_mem_moves_left_inv (by game_cmp))

noncomputable def g2 : IGame := !{{1} | ∅}

theorem g2_pos : 0 < g2 := by unfold g2; game_cmp

theorem g2_right : ∃ z, z ∈ g2⁻¹.moves .right :=
  ⟨_, invOption_mem_moves_inv (p₁ := .left) (p₂ := .right) g2_pos (y := 1) (by game_cmp)
    (by simp [g2]) (zero_mem_moves_left_inv g2_pos)⟩

-- `_private.CombinatorialGames.Game.IGame.0.IGame.invRec'`
theorem w_107 : ¬ drop0% _private.CombinatorialGames.Game.IGame.«0».IGame.invRec' 4 := fun h => by
  obtain ⟨z, hz⟩ := g2_right
  exact absurd (@h g2 g2_pos (fun p _ _ => p = .left) rfl .right z hz) (by decide)

-- `_private.CombinatorialGames.Game.IGame.0.IGame.invRec'`
theorem w_108 : ¬ indep0% _private.CombinatorialGames.Game.IGame.«0».IGame.invRec' 7 := fun h =>
  absurd (one_inv_moves _ _ (@h 1 (by game_cmp) (fun _ _ _ => True) trivial (fun _ _ _ _ _ _ _ _ => trivial)
    .right 0)).1 (by decide)

-- `IGame.invRec`
theorem w_109 : ¬ indep0% IGame.invRec 1 := fun h =>
  absurd (@h (-1) (fun _ _ _ => True) .right 0 zero_mem_negone_inv) (by game_cmp)

-- `IGame.invRec`
theorem w_110 : ¬ drop0% IGame.invRec 3 := fun h =>
  @h 1 (by game_cmp) (fun _ _ _ => False) (fun _ _ _ _ _ _ _ h => h) .left 0
    (zero_mem_moves_left_inv (by game_cmp))

-- `IGame.invRec`
theorem w_111 : ¬ drop0% IGame.invRec 4 := fun h => by
  obtain ⟨z, hz⟩ := g2_right
  exact absurd (@h g2 g2_pos (fun p _ _ => p = .left) rfl .right z hz) (by decide)

-- `IGame.invRec`
theorem w_112 : ¬ indep0% IGame.invRec 7 := fun h =>
  absurd (one_inv_moves _ _ (@h 1 (by game_cmp) (fun _ _ _ => True) trivial (fun _ _ _ _ _ _ _ _ => trivial)
    .right 0)).1 (by decide)

end W1c1

namespace W1c1
open IGame

-- helper: X = {∅ | 0, 1} is negative with the positive option 1
noncomputable def gX : IGame := !{∅ | {0, 1}}

theorem gX_neg_pos : 0 < -gX := by unfold gX; game_cmp

theorem negX_inv_moves : ∀ p y, y ∈ (-gX)⁻¹.moves p → p = .left ∧ y = 0 :=
  invMoves_triv gX_neg_pos (fun p y hy => by
    cases p <;> simp [gX] at hy
    rcases hy with rfl | rfl
    · exact lt_irrefl 0
    · game_cmp)

-- `IGame.invOption_mem_moves_inv`
theorem w_101 : ¬ drop0% IGame.invOption_mem_moves_inv 5 := fun h => by
  have e : gX⁻¹ = -(-gX)⁻¹ := by rw [← IGame.inv_neg, neg_neg]
  have ha : (0 : IGame) ∈ gX⁻¹.moves .right := by
    rw [e, moves_neg]; simpa using zero_mem_moves_left_inv gX_neg_pos
  have h1 := @h gX 1 0 .right .right (by game_cmp) (by simp [gX]) ha
  rw [e, moves_neg, Set.mem_neg] at h1
  have h3 : IGame.invOption gX 1 0 = 0 := neg_eq_zero.1 (negX_inv_moves _ _ h1).2
  have hm : _ ∈ (((1 : IGame) + (1 - gX) * 0) * (1 : IGame)⁻¹).moves .left :=
    mulOption_mem_moves_mul (px := .left) (py := .left) (x := 1 + (1 - gX) * 0) (a := 0 + (1 - gX) * 0)
      (by simp) (zero_mem_moves_left_inv (by game_cmp))
  have h4 : IGame.invOption gX 1 0 = ((1 : IGame) + (1 - gX) * 0) * (1 : IGame)⁻¹ := rfl
  rw [← h4, h3] at hm
  simp at hm

instance g2_num : Numeric g2 :=
  numeric_def.2 ⟨by simp [g2], fun p y hy => by cases p <;> simp [g2] at hy; subst hy; infer_instance⟩

-- `IGame.invOption_mem_moves_inv`
theorem w_104 : ¬ drop0% IGame.invOption_mem_moves_inv 8 := fun h => by
  have h1 := @h g2 1 IGame.star .left .right g2_pos (by game_cmp) (by simp [g2])
  have hn : Numeric (IGame.invOption g2 1 IGame.star) := Numeric.of_mem_moves h1
  have hu : 0 + -g2 ∈ (1 + -g2 : IGame).moves .left := add_right_mem_moves_add (by simp) (-g2)
  have hL : mulOption (1 - g2) IGame.star (0 + -g2) 0 ∈ ((1 - g2) * IGame.star).moves (.left * .left) :=
    mulOption_mem_moves_mul hu (by simp)
  have hR : mulOption (1 - g2) IGame.star (0 + -g2) 0 ∈ ((1 - g2) * IGame.star).moves (.left * .right) :=
    mulOption_mem_moves_mul hu (by simp)
  have hL2 := add_left_mem_moves_add hL 1
  have hR2 := add_left_mem_moves_add hR 1
  have hz := zero_mem_moves_left_inv (x := 1) (by game_cmp)
  have hL3 := mulOption_mem_moves_mul (py := .left) hL2 hz
  have hR3 := mulOption_mem_moves_mul (py := .left) hR2 hz
  exact lt_irrefl _ (@Numeric.left_lt_right _ _ _ hn hL3 hR3)

end W1c1

namespace W1c1
open IGame

theorem notImp1 : ¬ Impartial (1 : IGame) := fun h => absurd (impartial_def.1 h).1 (by game_cmp)

-- helper: Y = {-1 | 1} is ≈ 0 and Y = -Y, but not impartial
noncomputable def gY : IGame := !{{-1} | {1}}

theorem gY_equiv : gY ≈ 0 := by unfold gY; game_cmp

theorem gY_notImp : ¬ Impartial gY := fun h => by
  have h1 := (impartial_def.1 h).2 .left (-1) (by simp [gY])
  exact absurd (impartial_def.1 h1).1 (by game_cmp)

theorem gY_neg : -gY = gY := by simp [gY]

theorem gY_grundy_eq : grundyAux .left gY = grundyAux .right gY := by
  rw [← gY_neg, grundyAux_neg, gY_neg]; rfl

theorem gY_grundy_ne : grundyAux .right gY ≠ 0 := by
  have h1 : grundyAux .right (1 : IGame) = 0 := by rw [grundyAux_def]; simp
  have := grundyAux_ne (p := .right) (x := gY) (y := 1) (by simp [gY])
  rw [h1] at this; exact this.symm

-- `IGame.Impartial.nim_grundy_equiv`
theorem w_113 : ¬ indep0% IGame.Impartial.nim_grundy_equiv 1 := fun h => notImp1 (h 1)
-- `IGame.Impartial.grundy_eq_iff_equiv_nim`
theorem w_114 : ¬ indep0% IGame.Impartial.grundy_eq_iff_equiv_nim 1 := fun h => notImp1 (@h 1 0)
-- `IGame.Impartial.grundy_eq`
theorem w_115 : ¬ indep0% IGame.Impartial.grundy_eq 1 := fun h =>
  gY_notImp (@h gY 0 (by simpa using gY_equiv))
-- `IGame.Impartial.grundy_eq_zero_iff`
theorem w_116 : ¬ indep0% IGame.Impartial.grundy_eq_zero_iff 1 := fun h => notImp1 (@h 1)
-- `IGame.Impartial.grundy_eq_iff_equiv`
theorem w_117 : ¬ indep0% IGame.Impartial.grundy_eq_iff_equiv 2 := fun h => notImp1 (@h 1 0 Impartial.zero)
-- `IGame.Impartial.grundy_eq_iff_equiv`
theorem w_118 : ¬ indep0% IGame.Impartial.grundy_eq_iff_equiv 3 := fun h => notImp1 (@h 0 1 Impartial.zero)
-- `IGame.Impartial.grundy_neg`
theorem w_119 : ¬ indep0% IGame.Impartial.grundy_neg 1 := fun h => notImp1 (h 1)
-- `IGame.Impartial.grundyAux_eq_grundy`
theorem w_120 : ¬ indep0% IGame.Impartial.grundyAux_eq_grundy 2 := fun h => notImp1 (h .left 1)
-- `IGame.Impartial.grundy_add`
theorem w_121 : ¬ indep0% IGame.Impartial.grundy_add 2 := fun h => notImp1 (@h 1 0 Impartial.zero)
-- `IGame.Impartial.grundy_add`
theorem w_122 : ¬ indep0% IGame.Impartial.grundy_add 3 := fun h => notImp1 (@h 0 1 Impartial.zero)
-- `IGame.Impartial.grundy_moves_ne`
theorem w_123 : ¬ indep0% IGame.Impartial.grundy_moves_ne 3 := fun h => notImp1 (@h .left 1 0 (by simp))
-- `_private.CombinatorialGames.Game.Impartial.Grundy.0.IGame.Impartial.of_grundyAux_left_eq_grundyAux_right'`
theorem w_124 : ¬ drop0% _private.CombinatorialGames.Game.Impartial.Grundy.«0».IGame.Impartial.of_grundyAux_left_eq_grundyAux_right' 1 := fun h => by
  have e := (@h gY gY_grundy_eq).trans gY_equiv
  rw [← nim_zero, nim_equiv_iff] at e
  exact gY_grundy_ne e
-- `IGame.Impartial.of_grundyAux_left_eq_grundyAux_right`
theorem w_125 : ¬ drop0% IGame.Impartial.of_grundyAux_left_eq_grundyAux_right 1 := fun h =>
  gY_notImp (@h gY gY_grundy_eq)
-- `IGame.Impartial.of_grundyAux_left_eq_grundyAux_right`
theorem w_126 : ¬ drop0% IGame.Impartial.of_grundyAux_left_eq_grundyAux_right 2 := fun h =>
  notImp1 (@h 1 (fun p y hy => by cases p <;> simp at hy <;> subst hy <;> infer_instance))

end W1c1
