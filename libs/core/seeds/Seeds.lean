/-! Hand-made counterexamples for one theorem per cluster. Each shows `¬T'` (theorem without the
set_option warn.classDefReducibility false
hypothesis); the bad instances/functions are what a reusable model library would contain. -/

-- LawfulBEq: Bool where everything is `==`.
def allEq : BEq Bool := ⟨fun _ _ => true⟩

example : ¬ ∀ (α : Type) [BEq α] {a : α} {l : List α}, a ∈ l → l.Perm (a :: l.erase a) := by
  intro h
  have := @h Bool allEq true [false, true] (by decide)
  revert this; decide

example : ¬ ∀ (α : Type) [BEq α] {a : α} {as : List α}, as.contains a ↔ a ∈ as := by
  intro h
  have := @h Bool allEq true [false]
  revert this; decide

-- Std.Asymm (· < ·): a relation that is total.
def allLT : LT Bool := ⟨fun _ _ => True⟩

example : ¬ ∀ (α : Type) [LT α] {a b : α}, a < b → ¬ b < a := by
  intro h
  exact @h Bool allLT true true trivial trivial

-- Std.Associative op: implication on Bool.
example : ¬ ∀ {α : Type} {op : α → α → α} {xs : List α} {a₁ a₂ : α},
    xs.foldr op (op a₁ a₂) = op (xs.foldr op a₁) a₂ := by
  intro h
  have := @h Bool (fun a b => !a || b) [false] false false
  revert this; decide

-- Std.Associative min: NOR as `min`.
def norMin : Min Bool := ⟨fun a b => !a && !b⟩

example : ¬ ∀ {α : Type} [Min α] {a : α} {l : List α} {h},
    (a :: l).min h = l.min?.elim a (min a ·) := by
  intro h
  have := @h Bool norMin true [false, false] (by simp)
  revert this; decide

-- LawfulOrderLT: `<` unrelated to `≤`.
def leTriv : LE Bool := ⟨fun _ _ => True⟩

example : ¬ ∀ {α : Type} [LT α] [LE α] {a b : α}, a ≤ b → ¬ b < a := by
  intro h
  exact @h Bool allLT leTriv true true trivial trivial
