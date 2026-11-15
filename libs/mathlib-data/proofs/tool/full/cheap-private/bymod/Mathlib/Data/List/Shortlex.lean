import Mathlib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/
-- _private.Mathlib.Data.List.Shortlex.0.Acc.shortlex, hypothesis 5: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Acc.shortlex.h5.gneg.{u_1} : ∀ {α : Type u_1} {r : α → α → Prop} {a : α} {b : List α},
      Acc r a →
        ¬Acc (List.Shortlex r) b →
          (∀ (s : List α), s.length < (a :: b).length → Acc (List.Shortlex r) s) → Acc (List.Shortlex r) (a :: b) := by
  (intros; solve_by_elim)
theorem HypCheckProof.Acc.shortlex.h5.{u_1} : ∀ {α : Type u_1} {r : α → α → Prop} {a : α} {b : List α},
      Acc r a → (∀ (s : List α), s.length < (a :: b).length → Acc (List.Shortlex r) s) → Acc (List.Shortlex r) (a :: b) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x6
  exact Classical.byCases (fun hc_h => @Acc.shortlex hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_h hc_x6) (fun hc_hn => @HypCheckProof.Acc.shortlex.h5.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_hn hc_x6)
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Acc.shortlex.h5.derivable.{u_1} : ∀ {α : Type u_1} {r : α → α → Prop} {a : α} {b : List α},
      Acc r a → (∀ (s : List α), s.length < (a :: b).length → Acc (List.Shortlex r) s) → Acc (List.Shortlex r) b := by
  (intros; solve_by_elim)

