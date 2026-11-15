# Unresolved rows: obstructions

25 rows are neither proved removable nor refuted after the tool run, 47 agent clusters and two tail rounds. Each row was attempted by at least two agents; the obstruction below is the last agent's (full text in `results/unresolved_obstructions.jsonl`, field `prior_obstruction`). "Possibly removable" means the agent found no counter-model and suspects a proof exists.

## BI.Lib.Counterexamples (classic paradoxes) (16)

| Theorem | # | Hypothesis | Obstruction |
|---|---|---|---|
| `Iris.Inv.contradiction` | 21 | `finished_dup : ∀ (γ : gname), finished γ ⊢ finished γ ∗ finished γ` | neither derivable nor refuted: Inv2/Inv1 derivations need a persistent or duplicable finished witness inside the M0 opening, and inv_alloc (the only source of persistent witnesses) works only at M1; a model needs persistent impredicative invariants without la… |
| `Iris.Inv.contradiction'` | 18 | `inst : ∀ (γ : gname), Iris.BI.Persistent (finished γ)` | neither derivable nor refuted: Inv2/Inv1 derivations need a persistent or duplicable finished witness inside the M0 opening, and inv_alloc (the only source of persistent witnesses) works only at M1; a model needs persistent impredicative invariants without la… |
| `Iris.Inv.invariant_contradiction` | 8 | `fupd_mono : ∀ {E : Iris.Inv.Mask} {P Q : PROP}, (P ⊢ Q) → fupd E P ⊢ fup` | honest invariants (inv i X = □X with fupd M0 = id satisfy inv_fupd for any fupd M1 with intro) and pure cancellation invariants make the conclusion hold (A ⊇ saved False, plus T1c2's Lawvere argument); with start_finish/finished persistent start collapses to … |
| `Iris.Inv.saved_A` | 2 | `instAffine : Iris.BI.BIAffine PROP` | non-affine: the paradox itself goes through without affinity (contradiction idx 2 removable, <pers> instead of □), but saved_cast/saved_A use the library's □-based saved/A and leave a finished token over; a refutation needs dishonest persistent invariants in … |
| `Iris.Inv.saved_A` | 6 | `inst : ∀ (i : name) (P : PROP), Iris.BI.Persistent (inv i P)` | P-independent non-persistent invariants (inv = ownM credit, which refuted finished_contradiction idx 6) make saved P independent of P, so A ⊇ saved False = saved A; token-carrying dishonest invariants (ownM 1 ∗ ⌜Ok P⌝) make □A empty (A always holds the token)… |
| `Iris.Inv.saved_A` | 7 | `fupd_intro : ∀ {E : Iris.Inv.Mask} {P : PROP}, P ⊢ fupd E P` | honest invariants (inv i X = □X with fupd M0 = id satisfy inv_fupd for any fupd M1 with intro) and pure cancellation invariants make the conclusion hold (A ⊇ saved False, plus T1c2's Lawvere argument); with start_finish/finished persistent start collapses to … |
| `Iris.Inv.saved_A` | 8 | `fupd_mono : ∀ {E : Iris.Inv.Mask} {P Q : PROP}, (P ⊢ Q) → fupd E P ⊢ fup` | honest invariants (inv i X = □X with fupd M0 = id satisfy inv_fupd for any fupd M1 with intro) and pure cancellation invariants make the conclusion hold (A ⊇ saved False, plus T1c2's Lawvere argument); with start_finish/finished persistent start collapses to … |
| `Iris.Inv.saved_A` | 9 | `fupd_fupd : ∀ {E : Iris.Inv.Mask} {P : PROP}, fupd E (fupd E P) ⊢ fupd E` | honest invariants (inv i X = □X with fupd M0 = id satisfy inv_fupd for any fupd M1 with intro) and pure cancellation invariants make the conclusion hold (A ⊇ saved False, plus T1c2's Lawvere argument); with start_finish/finished persistent start collapses to … |
| `Iris.Inv.saved_A` | 10 | `fupd_frame_left : ∀ {E : Iris.Inv.Mask} {P Q : PROP}, P ∗ fupd E Q ⊢ fupd E ip` | honest invariants (inv i X = □X with fupd M0 = id satisfy inv_fupd for any fupd M1 with intro) and pure cancellation invariants make the conclusion hold (A ⊇ saved False, plus T1c2's Lawvere argument); with start_finish/finished persistent start collapses to … |
| `Iris.Inv.saved_A` | 15 | `start_finish : ∀ (γ : gname), start γ ⊢ fupd Iris.Inv.Mask.M0 (finished γ)` | honest invariants (inv i X = □X with fupd M0 = id satisfy inv_fupd for any fupd M1 with intro) and pure cancellation invariants make the conclusion hold (A ⊇ saved False, plus T1c2's Lawvere argument); with start_finish/finished persistent start collapses to … |
| `Iris.Inv.saved_A` | 16 | `finished_not_start : ∀ (γ : gname), start γ ∗ finished γ ⊢ False` | honest invariants (inv i X = □X with fupd M0 = id satisfy inv_fupd for any fupd M1 with intro) and pure cancellation invariants make the conclusion hold (A ⊇ saved False, plus T1c2's Lawvere argument); with start_finish/finished persistent start collapses to … |
| `Iris.Inv.saved_A` | 17 | `finished_dup : ∀ (γ : gname), finished γ ⊢ finished γ ∗ finished γ` | honest invariants (inv i X = □X with fupd M0 = id satisfy inv_fupd for any fupd M1 with intro) and pure cancellation invariants make the conclusion hold (A ⊇ saved False, plus T1c2's Lawvere argument); with start_finish/finished persistent start collapses to … |
| `Iris.Inv.saved_NA` | 8 | `fupd_mono : ∀ {E : Iris.Inv.Mask} {P Q : PROP}, (P ⊢ Q) → fupd E P ⊢ fup` | honest invariants (inv i X = □X with fupd M0 = id satisfy inv_fupd for any fupd M1 with intro) and pure cancellation invariants make the conclusion hold (A ⊇ saved False, plus T1c2's Lawvere argument); with start_finish/finished persistent start collapses to … |
| `Iris.Inv.saved_cast` | 2 | `instAffine : Iris.BI.BIAffine PROP` | non-affine: the paradox itself goes through without affinity (contradiction idx 2 removable, <pers> instead of □), but saved_cast/saved_A use the library's □-based saved/A and leave a finished token over; a refutation needs dishonest persistent invariants in … |
| `Iris.Inv.saved_cast` | 8 | `inst : ∀ (i : name) (P : PROP), Iris.BI.Persistent (inv i P)` | P-independent non-persistent invariants (inv = ownM credit, which refuted finished_contradiction idx 6) make saved P independent of P, so A ⊇ saved False = saved A; token-carrying dishonest invariants (ownM 1 ∗ ⌜Ok P⌝) make □A empty (A always holds the token)… |
| `Iris.Inv.saved_cast` | 11 | `fupd_fupd : ∀ {E : Iris.Inv.Mask} {P : PROP}, fupd E (fupd E P) ⊢ fupd E` | honest invariants (inv i X = □X with fupd M0 = id satisfy inv_fupd for any fupd M1 with intro) and pure cancellation invariants make the conclusion hold (A ⊇ saved False, plus T1c2's Lawvere argument); with start_finish/finished persistent start collapses to … |

## ProgramLogic (mask inclusions, invariant opening) (6)

| Theorem | # | Hypothesis | Obstruction |
|---|---|---|---|
| `Iris.inv_open_maybe_ectxlang` | 15 | `Hsub : E₂ ⊆ E₁` | only the atomic-redex case with both disjuncts under the outer \|={E₁,E₂}=> is open; the right disjunct needs wp E₁ e Φ ⊢ wp E₁ e (\|={E₁,E₂}=> \|={E₂,E₁}=> Φ) (mask intro needs E₂ ⊆ E₁); every lawful atomic wp tried (\|={E}=> Φ, \|={E,⊤}=> \|={⊤,E}=> Φ, ∃-mask clo… |
| `Iris.twp.to_wp_fupdN_strong` | 16 | `HSub : E₂ ⊆ E₁` | as wp_step_fupdN_strong 16 (premise \|={E₁,E₂}=> £ n ={∅}▷=∗^[n] \|={E₂,E₁}=> P needs the E₂∖E₁ tokens) |
| `Iris.wp_frame_step_l` | 15 | `E₂E₁ : E₂ ⊆ E₁` | as wp_step_fupd 15 (premise \|={E₁}[E₂]▷=> R needs the E₂∖E₁ tokens) |
| `Iris.wp_frame_step_r` | 15 | `h2 : E₂ ⊆ E₁` | as wp_step_fupd 15 (premise \|={E₁}[E₂]▷=> R needs the E₂∖E₁ tokens) |
| `Iris.wp_step_fupd` | 15 | `E₂E₁ : E₂ ⊆ E₁` | E₂ ⊄ E₁ with the step update \|={E₁}[E₂]▷=> R: the dropped-inclusion trick of this cluster (mask_route: token own1 γ plus an invariant allocated open with its closer discarded, so WP at ⊤ is logically trivial and WP at ⊤∖N refutable) needs E₂∖E₁ ⊇ ↑N, whose to… |
| `Iris.wp_step_fupdN_strong` | 16 | `E2_E1 : E2 ⊆ E1` | as wp_step_fupd 15: premise \|={E1,E2}=> \|={∅}▷=>^[n] \|={E2,E1}=> P needs the E2∖E1 tokens even for n = 0 (unlike wp_step_fupdN, whose premise lives at E₁∖E₂) |


## Instances.Lib (boxes/slices) (3)

| Theorem | # | Hypothesis | Obstruction |
|---|---|---|---|
| `Iris.slice_combine` | 16 | `HE : ↑N ⊆ E` | same as slice_split 16 |
| `Iris.slice_iff` | 15 | `HE : ↑N ⊆ E` | same as slice_split 16 (the new slice γ' with Q' ≠ Q needs ▷Q' from the old invariant; same namespace N prevents having both copies open at once; the lemma's existential γ' may coincide with γ) |
| `Iris.slice_split` | 16 | `HE : ↑N ⊆ E` | as before: the b = true branch needs Q1 ∗ Q2 out of the old slice invariant; a refutation must use the stuck copy, but after the lemma the old flag fragment ◯E b is only reachable by opening the old invariant and b is unknown without the old auth (consumed); … |
