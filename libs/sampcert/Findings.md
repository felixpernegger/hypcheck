# Findings: SampCert

Concrete defects found along the way, beyond the list of removable hypotheses (`Results.md`). Nothing has been reported upstream yet.

## `SLang.privComposeAdaptive_renyi_bound` holds with no hypotheses
`SampCert/DifferentialPrivacy/ZeroConcentrated/AdaptiveComposition.lean` l.37: the Rényi composition bound `D(compose l₁ ‖ compose l₂) ≤ D(nq1 l₁ ‖ nq1 l₂) + ⨆ u, D(nq2 u l₁ ‖ nq2 u l₂)` holds for every real α and any lists, without `1 < α`, `Neighbour l₁ l₂`, `ACNeighbour nq1`, `∀ u, ACNeighbour (nq2 u)` — all four jointly (`T1c5.genAll` in `checks/T1c5Hand.lean`). The AC/Neighbour hypotheses only fed `RenyiDivergence_def_nonneg`, which itself does not need AbsCts for 1 < α (the series is ⊤ without it).
