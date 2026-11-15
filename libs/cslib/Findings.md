# Findings: CSLib

No CSLib defect beyond unneeded hypotheses was found. The removable hypotheses are listed in
`results/removable_review.md`; groups worth an upstream cleanup:
- 15 × `[Nonempty Output]` in `Cslib.Crypto.PRG.Generator`, derivable from `[Nonempty Seed]` and the generator;
- `[IsOrderedRing R]` in `Polynomial.monotone_eval`/`eval_mono`, derivable (Mathlib's `toIsOrderedRing` needs
  `CommSemiring`);
- `Nat.segment_zero`: both hypotheses unneeded, also jointly.

Nothing has been reported upstream yet.
