# Findings: iris-lean library defects worth reporting upstream

Concrete defects found along the way, beyond the list of removable hypotheses (`results/removable_review.md`). One entry per defect: declaration, file:line, what is wrong, evidence, suggested fix. None has been reported upstream yet.

## `FromMathlib.Pairwise.forall` carries three unneeded hypotheses

`Iris/Std/FromMathlib.lean:20`: `theorem Pairwise.forall {l} {R} (hR : ∀ {a b}, R a b ↔ a ≠ b) (hl : l.Pairwise (· ≠ ·)) : ∀ ⦃a⦄, a ∈ l → ∀ ⦃b⦄, b ∈ l → a ≠ b → R a b`. With `hR` the conclusion `a ≠ b → R a b` holds outright, so `hl`, `a ∈ l` and `b ∈ l` are each removable (HypCheck, `simp_all`; stored proofs in `proofs/tool/full/public`). Mathlib's original takes `Symmetric R` instead of `hR`; the copy replaced that by an iff with `≠` but kept the list hypotheses. Suggested fix: drop the lemma or state it as `(hR : ∀ {a b}, R a b ↔ a ≠ b) : a ≠ b → R a b`, or restore Mathlib's `Symmetric R` form.

## `OrdCommMonoidLike.instCancelable` can only apply to trivial types

`Iris/Algebra/Numbers.lean:215` (section for `(α, max)`-style "Universal Core" ORAs): `scoped instance instCancelable [LeftCancelAdd α] {a : α} : Cancelable a`, copied from the `(ℕ, +)` section (line 100). In this section `+` is idempotent and commutative (`max`), and an idempotent left-cancellative operation forces `y + x = x` for all `x, y`, hence (with commutativity) `x = y`: every such `α` has at most one element, so the instance never applies to `MaxNat`/`MaxInt`/`MinNat` (which are not left-cancellative) and is vacuous. Evidence: its `[OFE.Discrete α]` hypothesis is derivable for exactly this reason (W3c0, `checks/W3c0Hand.lean:692`, `indep%`). Suggested fix: drop the instance from this section.

## `BI/Lib/Relations.lean`: `[NonExpansive₂ R]` is unneeded on most rtc/tc lemmas

`Iris/BI/Lib/Relations.lean`: the section variable `[NonExpansive₂ R]` reaches 15 lemmas that do not need it: `bi_rtc_{refl,left,once,trans,right,strong_ind_left,persistent}` and `bi_tc_{left,once,trans,right,rtc_left,rtc,absorbing,persistent,strong_ind_left}` (hypothesis idx 5 each). The library proves introduction via `bi_least_fixpoint_unfold`, which needs `BIMonoPred` and hence non-expansiveness; unfolding the impredicative definition (`∀ Φ, □(pre Φ → Φ) → Φ x`) directly proves the introduction rules for every `R`, and induction only needs first-argument non-expansiveness of `biRtc/biTc R · y`, which holds for every `R` (W5c4, `checks/W5c4Hand.lean:95–250`). Also unneeded: `NonExpansive Φ` in `bi_{rtc,tc}_strong_ind_left` (idx 8) and `Timeless emp`/`Discrete A` in `bi_tc_timeless` (idx 3/5, via the k-fold unrolling `biTc = ∃ k, itT k`). Suggested fix: prove intro rules by unfolding and drop the instance from those lemmas (via `omit … in` or a narrower section).

## `Linear.leak` (and its section variables) quantify over auto-bound `M0`/`M1` instead of the `Mask` constructors

`Iris/BI/Lib/Counterexamples.lean:482–533`: `namespace Linear` defines its own `inductive Mask where | M0 | M1` but, unlike the earlier section (line 165), never does `open Mask`. So `M0`/`M1` in `variable (cinv_acc : … fupd M1 M0 …)` and in `theorem leak : P ⊢ fupd M1 M1 emp` are auto-bound implicit variables: the elaborated `Iris.Linear.leak` starts with `{M1 M0 : Iris.Linear.Mask}`. The statement is therefore "for all masks M0 M1", stronger than the intended Rocq lemma (fixed masks ⊤ and ⊤∖N), and the `Mask` constructors are unused. It still holds (the proof goes through), so this is a fidelity/style defect, not an unsoundness. Suggested fix: add `open Mask` after the inductive (or write `.M0`/`.M1`), and consider `set_option autoImplicit false` for the file.


## `fupd_vs_trans` does not need `[IncOrd M]` (nor `vs_impl`)

`Iris/Instances/Lib/FUpdFromViewShift.lean:65`: `theorem fupd_vs_trans [IncOrd M] … (vs_impl : …)`. The Rocq original lives in `uPred`, which is always affine. The Lean port generalises to any UORA and adds `[IncOrd M]` (affinity), but the lemma holds without it. Affinity is only used to turn the library's `emp ⊢ vs₂₃ Q P` into `vs₁₂ R Q ⊢ vs₂₃ Q P`. A different witness avoids that step entirely. (The proof idea came from an external model and was checked here.)

- `persistent_intro_r` with the persistent `T := vs(A,B)` gives `emp ⊢ vs(A ∗ vs(A,B), B)`.
- Hence, with `vs_exists`, `emp ⊢ vs₂₃ (fupd₂₃ P) P`.
- Take the whole left-hand resource `W := A ∗ vs₁₂ A Q` as the new existential witness. Then `emp ⊢ vs₁₂ W Q`, `trans` gives `emp ⊢ vs₁₃ W P`, and `W ⊢ W ∗ vs₁₃ W P ⊢ fupd₁₃ P`.

**Evidence:** `checks/T3c6Hand.lean` `t3c6_0` (`[IncOrd M]` dropped) and `checks/J4c0Hand.lean` `j4_0` (`[IncOrd M]` and `vs_impl` dropped together). Both are kernel-checked with standard axioms. The other three hypotheses are necessary (Lean counter-models in `checks/T3c6Hand.lean`). `vs_impl` alone was already known to be removable (`checks/Probe3Hand.lean`). `[IncOrd M]` stays necessary for the sibling `fupd_vs_mono` (`checks/T1c5Hand.lean`).

**Suggested fix:** drop `[IncOrd M]` and `vs_impl` from `fupd_vs_trans`, using the proof above.
