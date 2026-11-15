# Results: SampCert

Which Prop-valued hypotheses of the theorems in [SampCert](https://github.com/leanprover/SampCert) (verified
differential-privacy samplers) are needed? How verdicts are defined, found and checked: `../../Methods.md`.

- **Library version:** commit `a2c53bb` (2026-09-25).
- **Toolchain:** `leanprover/lean4:v4.34.1`, Mathlib from the library's manifest.
- **Scope:** all theorems with a Prop-valued parameter in modules under `SampCert` (no private theorem has one).
- **Analysis only:** no file of the library was changed.

## Summary

All 607 hypotheses in 331 theorems are decided, every verdict with a kernel-checked Lean proof using only the
standard axioms: **418 necessary, 189 removable, 0 independent, 0 unresolved.** The removable share (31%) is much
higher than in the other libraries analysed here.

| Folder | Theorems | Hypotheses | Necessary | Removable |
|---|---|---|---|---|
| DifferentialPrivacy | 182 | 404 | 255 | 149 |
| Samplers | 72 | 99 | 86 | 13 |
| Util | 59 | 85 | 58 | 27 |
| Foundations | 14 | 14 | 14 | 0 |
| SLang and root | 4 | 5 | 5 | 0 |
| **total** | **331** | **607** | **418** | **189** |

## How the verdicts were reached

| Source | Necessary | Removable |
|---|---|---|
| hand proofs by AI agents (probe, one wave of 3 clusters, tails) and the main session | 290 | 142 |
| `HypCheck.lean` v12, including proof repair (6 removable) | 111 | 27 |
| transitive necessity and removability | 17 | 15 |
| unused in the library's own proof | | 5 |

## Removable hypotheses (189)

- Measure-theory instances `[Countable _]`, `[MeasurableSingletonClass _]`, `[DiscreteMeasurableSpace _]` in the
  Rényi, zCDP and post-processing files: restrict to the countable support, or use the discrete σ-algebra when the
  statement does not mention it.
- `AbsCts` hypotheses: derivable from a finite Rényi bound, or the conclusion holds anyway because the series is ⊤.
- `σ ≠ 0` in discrete-Gaussian and Poisson-summation lemmas (σ = 0 degenerates consistently), summability in
  `tsum_shift*` (shift invariance over ℤ), `γ ≠ ⊤` in sampler lemmas.
- `SLang.privComposeAdaptive_renyi_bound` holds with none of its four hypotheses, jointly (`Findings.md`).

SampCert runs no unused-arguments linter. Only the 5 structurally unused hypotheses would be visible to one; the other
184 removable hypotheses are used by the proofs but not needed.

## Necessary hypotheses worth noting

- At δ = 0, Lean's `Real.log (1/0) = 0` collapses the approximate-DP bound of `ApproximateDP_of_zCDP*` and
  `zCDP_ApproximateDP` to pure DP (`checks/T1c0Hand.lean`).
- The Gaussian Rényi bounds fail for α = 1/2 at σ = 1/4 (`checks/T1c1Hand.lean`); the noised-query zCDP bound without
  sensitivity fails exactly at α = 2 (`checks/T1c2Hand.lean`).
- The above-threshold, sparse and unbounded-max mechanisms are non-constant, are not DP for large-sensitivity queries,
  and lose mass without `has_lucky` (`checks/T1c3Hand.lean`, `T1c4Hand.lean`, `T1c6Hand.lean`).

## Library-specific method notes

- Tool: kit `HypCheck.lean` v12. Five stored tool proofs (`exact?`/`simp_all` over ℝ and `ENNReal`) timed out in a
  fresh compile under their recorded heartbeat limit; raising the limit in the stored file (to 200000) fixed them.

## Caveats

- Each hypothesis is checked on its own (except the joint result for `privComposeAdaptive_renyi_bound`).
- Removing a hypothesis from a public lemma breaks its callers.

## Where things are

| What | Where |
|---|---|
| All verdicts | `results/public.jsonl` (+ `_removable`) |
| Library defect | `Findings.md` |
| Stored proofs | `checks/*.lean`; tool proofs in `proofs/tool/` |
