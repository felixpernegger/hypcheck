set_option warn.classDefReducibility false
def countM : Monad (fun α => Nat × α) :=
  { pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) }

example : ¬ ∀ (f : Nat → Nat × Nat) (l : List Nat),
    @List.mapM' (fun α => Nat × α) Nat Nat countM f l = @List.mapM (fun α => Nat × α) countM Nat Nat f l := by
  intro h
  have := h (fun n => (0, n)) [0]
  revert this; decide
