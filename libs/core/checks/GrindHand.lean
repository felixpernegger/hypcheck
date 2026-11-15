/-!
Hand verdicts for grind lemmas whose automatically found counterexample could not be stored as a
checked proof (see `Results.md`, v7 grind recheck). Run with the lean4 repo's stage1 binary:
`lean checks/GrindHand.lean`.
-/

open Lean.Grind CommRing

-- As in `Init/Grind/Ring/Kronecker.lean`, so that `(c : α)` for `c : Nat` elaborates the same way.
attribute [local instance] Semiring.natCast Ring.intCast

-- `Lean.Grind.CommRing.Expr.toLinQ_spec` (`hf`): `invs := [(0, 0)]` records variable 0 as the
-- inverse of `0`, so `toLinQ invs (.var 0) = (.num 1, 0)` and the conjunct
-- `(e.toLinQ invs).2 ≠ 0` fails, for any `f` (here `fun _ => 0` over `Rat`).
example : ¬ ∀ {α : Type} [Field α] [IsCharP α 0] (f : Nat → α) (K : Nat) (invs : InvVars)
    (e : Expr), e.degQL_k invs ≤ 1 →
    (e.toLinQ invs).1.denoteG (PPoly.linVal f) = (((e.toLinQ invs).2 : Nat) : α) * e.denoteF f ∧
    (e.toLinQ invs).2 ≠ 0 ∧
    (e.toLinQ invs).1.kron (2 ^ K) = (e.kronQLin_k K invs).1 ∧
    (e.toLinQ invs).2 = (e.kronQLin_k K invs).2 ∧
    (e.toLinQ invs).1.norm1 ≤ (e.majQ_k invs).1 ∧ (e.toLinQ invs).2 = (e.majQ_k invs).2 := by
  intro h
  have := (h (α := Rat) (fun _ => 0) 0 [(0, 0)] (.var 0) (by decide)).2.1
  exact this (by decide)

-- Transcription check: the same statement with `hf` put back is the library theorem.
example : ∀ {α : Type} [Field α] [IsCharP α 0] (f : Nat → α) (K : Nat) (invs : InvVars),
    (∀ x c, InvVars.lookup_k invs x = some c → f x = (c : α)⁻¹ ∧ c ≠ 0) →
    ∀ (e : Expr), e.degQL_k invs ≤ 1 →
    (e.toLinQ invs).1.denoteG (PPoly.linVal f) = (((e.toLinQ invs).2 : Nat) : α) * e.denoteF f ∧
    (e.toLinQ invs).2 ≠ 0 ∧
    (e.toLinQ invs).1.kron (2 ^ K) = (e.kronQLin_k K invs).1 ∧
    (e.toLinQ invs).2 = (e.kronQLin_k K invs).2 ∧
    (e.toLinQ invs).1.norm1 ≤ (e.majQ_k invs).1 ∧ (e.toLinQ invs).2 = (e.majQ_k invs).2 :=
  @Expr.toLinQ_spec
