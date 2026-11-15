# Removable hypotheses in CSLib

All 105 verdicts have a kernel-checked stored proof of `T'` (the theorem without the hypothesis). Each hypothesis is removable **on its own**; pairs marked "each" are removable individually, not jointly. `kind`: *derivable* = follows from the other binders; *unneeded* = the conclusion holds without it. These are candidates for review, not proposed changes.

| # | Theorem (module) | idx | Hypothesis | Source | Note |
|---|---|---|---|---|---|
| 1 | `Cslib.Algorithms.Lean.TimeM.clog2_half_le` (Algorithms.Lean.MergeSort.MergeSort) | 1 | `h : 1 < n` | W1c0 | n = 0, 1: both sides 0 |
| 2 | `Cslib.Algorithms.Lean.TimeM.clog2_floor_half_le` (Algorithms.Lean.MergeSort.MergeSort) | 1 | `h : 1 < n` | W1c0 | n = 0, 1: both sides 0 |
| 3 | `Cslib.Automata.NA.concat_run_left_right` (Computability.Automata.NA.Concat) | 9 | `hn : 0 < n` | W1c0 | n = 0: the run starts right, so na1 accepts [] |
| 4 | `Cslib.Automata.NA.FinAcc.loop_language_eq` (Computability.Automata.NA.Loop) | 4 | `h : ¬Cslib.Automata.Acceptor.language na = 0` | W1c0 | if na accepts nothing, a path of the loop back to the hub is empty, so both sides are {[]} |
| 5 | `Cslib.Automata.TwoWayNACfg.eta` (Computability.Automata.TwoWayNA.Basic) | 5 | `h' : ↑c.pos < input.length + 1` | hypcheck-v111 |  |
| 6 | `Cslib.Circuits.Boolean.Lupanov.mainTerm_le` (private) (Computability.Circuit.Boolean.Lupanov) | 2 | `hn : 5 * n.log2 < n` | hypcheck-v111 |  |
| 7 | `Cslib.Circuits.Boolean.Lupanov.error_le` (private) (Computability.Circuit.Boolean.Lupanov) | 3 | `hn : 3 * n.log2 ≤ n` | W1c0 | if 3 log₂ n > n then n ≤ 8, the exponent is 0 and c ≤ 1 |
| 8 | `Cslib.Circuits.Line.card` (Computability.Circuit.Finite) | 1 | `inst : Finite σ.Op` | W2c0 | if the sigma type is infinite, so is the support of the finsum; both sides are then 0 |
| 9 | `Cslib.Circuits.Program.card` (Computability.Circuit.Finite) | 1 | `inst : Finite σ.Op` | W2c0 | product of line counts; Line.card holds without finiteness |
| 10 | `Cslib.Circuits.fullInterpretation_isComplete_two` (private) (Computability.Circuit.Full) | 1 | `inst : Finite U` | W2c0 | on an infinite carrier, pair the inputs injectively with U × U ≃ U, then one gate decodes |
| 11 | `Cslib.Circuits.fullInterpretation_isComplete` (Computability.Circuit.Full) | 2 | `inst : Finite U` | W2c0 | the binary full basis is complete on every carrier |
| 12 | `Cslib.Circuits.instIsCompleteFullInterpretation` (Computability.Circuit.Full) | 2 | `inst : Finite U` | W2c0 | same argument |
| 13 | `Cslib.Circuits.Shannon.exists_hard_function` (Computability.Circuit.Shannon) | 2 | `inst : Finite σ.Op` | W2c0 | simulate by the finite binary full basis, one gate per gate |
| 14 | `Cslib.Circuits.Shannon.exists_hard_function` (Computability.Circuit.Shannon) | 3 | `inst : Finite U` | W2c0 | infinite U: Nat.card U = 0, and a constant needs a gate |
| 15 | `Cslib.FLP.FairScheduler.omega_forall_actions` (Computability.Distributed.FLP.FairScheduler) | 10 | `hd : a.FairDeliverMsg d ps q` | W2c3 | every flattened action is an action of some segment, which satisfies r without fairness of d, or the default none |
| 16 | `Cslib.FLP.FairScheduler.omega_forall_actions` (Computability.Distributed.FLP.FairScheduler) | 12 | `hs0 : q s0` | W2c3 | same argument; q s0 is not used |
| 17 | `Cslib.FLP.OnePseudoConsensus.nonUniform_init` (Computability.Distributed.FLP.Impossibility) | 8 | `hc : 2 ≤ Fintype.card P` | W2c3 | dependent; 1-pseudo-consensus forces card P ≥ 2 |
| 18 | `Cslib.FLP.OnePseudoConsensus.not_terminating` (Computability.Distributed.FLP.Impossibility) | 8 | `hc : 2 ≤ Fintype.card P` | W2c3 | 1-pseudo-consensus forces card P ≥ 2 |
| 19 | `Cslib.FLP.OnePseudoConsensus.canDecideWithout_uniform` (Computability.Distributed.FLP.OnePseudoConsensus) | 16 | `hd : a.CanDecideWithout s p b` | W2c3 | hd follows from hpc1, hr and hdn: canDecideWithout_exists gives some b' with CanDecideWithout s p b', and hdn rules out b' = !b |
| 20 | `Cslib.FLP.OnePseudoConsensus.nonUniform_inp` (Computability.Distributed.FLP.OnePseudoConsensus) | 8 | `hc : 2 ≤ Fintype.card P` | W2c3 | for card P ≤ 1 there is no 1-pseudo-consensus algorithm: with ps = ∅ the start state would have to be decided |
| 21 | `Cslib.FLP.ZeroFaultAlg.inv_tr_left` (Computability.Distributed.FLP.ZeroConsensus) | 1 | `npos : 0 < n` | W1c1 | the message m has a destination in Fin n |
| 22 | `Cslib.FLP.ZeroFaultAlg.inv_tr_right` (Computability.Distributed.FLP.ZeroConsensus) | 1 | `npos : 0 < n` | W1c1 | the message m has a destination in Fin n |
| 23 | `Cslib.FLP.ZeroFaultAlg.left_leadsTo_right` (Computability.Distributed.FLP.ZeroConsensus) | 1 | `npos : 0 < n` | W1c1 | p : Fin n gives 0 < n |
| 24 | `Cslib.FLP.ZeroFaultAlg.right_leadsTo_out` (Computability.Distributed.FLP.ZeroConsensus) | 1 | `npos : 0 < n` | W1c1 | p : Fin n gives 0 < n |
| 25 | `Cslib.Automata.NA.FinAcc.nfa_single_start_accept_eq_regex` (Computability.Languages.KleeneAlgorithm) | 7 | `hstart : nfa.start = {s}` | W1c1 | Kleene: `Cslib.Automata.NA.FinAcc.nfa_eq_regex` needs no start condition |
| 26 | `Cslib.Automata.NA.FinAcc.nfa_single_start_accept_eq_regex` (Computability.Languages.KleeneAlgorithm) | 8 | `haccept : nfa.accept = {t}` | W1c1 | Kleene: `Cslib.Automata.NA.FinAcc.nfa_eq_regex` needs no accept condition |
| 27 | `Language.dfa_num_state_ge` (Computability.Languages.MyhillNerode) | 3 | `inst : Finite ↑ws` | hypcheck-v111 |  |
| 28 | `Cslib.Automata.DA.FinAcc.unique_minimal` (Computability.Languages.MyhillNerode) | 3 | `inst : Finite State` | W1c1 | regularity makes the Nerode quotient finite and nonempty, so Nat.card State ≠ 0 forces State finite |
| 29 | `Cslib.Automata.DA.FinAcc.unique_minimal` (Computability.Languages.MyhillNerode) | 5 | `hr : l.IsRegular` | W1c1 | a finite DFA accepting l makes l regular |
| 30 | `Turing.moveInputPos_neg_of_ne_left` (Computability.Machines.Turing.MultiTape.Configuration) | 2 | `h : p ≠ 0` | hypcheck-v111 |  |
| 31 | `Turing.MultiTapeNTM.RunPath.exists_running` (Computability.Machines.Turing.MultiTape.Nondeterministic) | 6 | `h : (RelSeries.last p).Halted` | W2c4 | if the last configuration is running, no configuration of the path is halted (halted configs stay), so the path itself is a running path |
| 32 | `Turing.MultiTapeTM.workTapePos_runFrom_rewindWork` (Computability.Machines.Turing.MultiTape.Plumbing.RewindWork) | 9 | `hp : p ≤ w.length` | W2c4 | for p > w.length the head visits p, p - 1, p and halts: always in [-1, p] |
| 33 | `Cslib.BitString.flipBlock_erase` (Computability.QueryComplexity.Defs) | 3 | `hi : i ∈ B` | hypcheck-v111 |  |
| 34 | `Cslib.URM.evalState_toStandardForm_regs` (Computability.URM.StandardForm) | 2 | `hp : (Cslib.URM.evalState p inputs).Dom` | W3c0 | hp follows from hq (Halts.of_toStandardForm) |
| 35 | `Cslib.URM.evalState_toStandardForm_regs` (Computability.URM.StandardForm) | 3 | `hq : (Cslib.URM.evalState p.toStandardForm inputs).Dom` | W3c0 | hq follows from hp (Halts.toStandardForm) |
| 36 | `Cslib.Crypto.PRG.Family.Secure.of_admissible` (Crypto.Primitives.PRG.Asymptotic) | 5 | `inst : ∀ (n : ℕ), Nonempty (Output n)` | W3c0 | Nonempty Output follows from G and Nonempty Seed |
| 37 | `Cslib.Crypto.PRG.Family.SecureWithError.secure` (Crypto.Primitives.PRG.Asymptotic) | 5 | `inst : ∀ (n : ℕ), Nonempty (Output n)` | W3c0 | Nonempty Output follows from G and Nonempty Seed |
| 38 | `Cslib.Crypto.PRG.Family.not_secure_of_rangeAdversary` (Crypto.Primitives.PRG.Asymptotic) | 5 | `inst : ∀ (n : ℕ), Nonempty (Output n)` | W3c0 | Nonempty Output follows from G and Nonempty Seed |
| 39 | `Cslib.Crypto.PRG.Family.not_secure_of_two_mul_card_le` (Crypto.Primitives.PRG.Asymptotic) | 5 | `inst : ∀ (n : ℕ), Nonempty (Output n)` | W3c0 | Nonempty Output follows from G and Nonempty Seed |
| 40 | `Cslib.Crypto.PRG.Generator.advantage_nonneg` (Crypto.Primitives.PRG.Basic) | 5 | `inst : Nonempty Output` | W3c1 | Nonempty Output follows from Nonempty Seed and G |
| 41 | `Cslib.Crypto.PRG.Generator.advantage_le_one` (Crypto.Primitives.PRG.Basic) | 5 | `inst : Nonempty Output` | W3c1 | Nonempty Output follows from Nonempty Seed and G |
| 42 | `Cslib.Crypto.PRG.Generator.secure_one` (Crypto.Primitives.PRG.Basic) | 5 | `inst : Nonempty Output` | W3c1 | Nonempty Output follows from Nonempty Seed and G |
| 43 | `Cslib.Crypto.PRG.Generator.advantage_const` (Crypto.Primitives.PRG.Basic) | 5 | `inst : Nonempty Output` | W3c1 | Nonempty Output follows from Nonempty Seed and G |
| 44 | `Cslib.Crypto.PRG.Generator.secure_zero_of_outputDist_eq` (Crypto.Primitives.PRG.Basic) | 5 | `inst : Nonempty Output` | W3c1 | Nonempty Output follows from Nonempty Seed and G |
| 45 | `Cslib.Crypto.PRG.Generator.secure_zero_iff_outputDist_eq_uniform` (Crypto.Primitives.PRG.Basic) | 5 | `inst : Nonempty Output` | W3c1 | Nonempty Output follows from Nonempty Seed and G |
| 46 | `Cslib.Crypto.PRG.Generator.Secure.mono` (Crypto.Primitives.PRG.Basic) | 5 | `inst : Nonempty Output` | W3c1 | Nonempty Output follows from Nonempty Seed and G |
| 47 | `Cslib.Crypto.PRG.Generator.Secure.of_admissible` (Crypto.Primitives.PRG.Basic) | 5 | `inst : Nonempty Output` | W3c1 | Nonempty Output follows from Nonempty Seed and G |
| 48 | `Cslib.Crypto.PRG.Generator.advantage_rangeAdversary` (Crypto.Primitives.PRG.Basic) | 5 | `inst : Nonempty Output` | W3c1 | Nonempty Output follows from Nonempty Seed and G |
| 49 | `Cslib.Crypto.PRG.Generator.one_sub_card_div_le_advantage_rangeAdversary` (Crypto.Primitives.PRG.Basic) | 5 | `inst : Nonempty Output` | W3c1 | Nonempty Output follows from Nonempty Seed and G |
| 50 | `Cslib.Crypto.PRG.Generator.not_secure_of_rangeAdversary` (Crypto.Primitives.PRG.Basic) | 5 | `inst : Nonempty Output` | W3c1 | Nonempty Output follows from Nonempty Seed and G |
| 51 | `Cslib.Crypto.PRG.Generator.not_secure_zero_of_isExpanding` (Crypto.Primitives.PRG.Basic) | 5 | `inst : Nonempty Output` | W3c1 | Nonempty Output follows from Nonempty Seed and G |
| 52 | `Cslib.Crypto.PRG.Generator.idealExperiment_leftReduction` (Crypto.Primitives.PRG.Basic) | 5 | `inst : Nonempty Output` | W3c1 | Nonempty Output follows from Nonempty Seed and G |
| 53 | `Cslib.Crypto.PRG.Generator.advantage_prod_le` (Crypto.Primitives.PRG.Basic) | 5 | `inst : Nonempty Output` | W3c1 | Nonempty Output follows from Nonempty Seed and G |
| 54 | `Cslib.Crypto.PRG.Generator.Secure.prod` (Crypto.Primitives.PRG.Basic) | 5 | `inst : Nonempty Output` | W3c1 | Nonempty Output follows from Nonempty Seed and G |
| 55 | `Cslib.Crypto.Protocols.SecretSharing.Shamir.scheme_authorized_iff` (Crypto.Protocols.SecretSharing.Shamir) | 6 | `inst : Nonempty F` | W3c1 | a field is nonempty |
| 56 | `Nat.eventually_mul_log_le` (Foundations.Data.Nat.Asymptotics) | 2 | `hb : 1 < b` | W1c2 | for b <= 1, Nat.log b n = 0 so the bound holds trivially |
| 57 | `Nat.nth_succ_gap` (Foundations.Data.Nat.Segment) | 1 | `hf : (Set.ofPred p).Infinite` | W1c2 | Nat.le_nth_of_lt_nth_succ needs no infinitude; for finite p the gap is between consecutive elements or empty |
| 58 | `Nat.segment_zero` (Foundations.Data.Nat.Segment) | 1 | `hm : StrictMono f` | Probe1 | segment f 0 = count (· ∈ range f) 1 - 1 ≤ 0 for every f (StrictMono unused; h0 too) |
| 59 | `Nat.segment_zero` (Foundations.Data.Nat.Segment) | 2 | `h0 : f 0 = 0` | W1c2 | segment f 0 = 0 for every f (count over {0} minus 1) |
| 60 | `Nat.segment_upper_bound` (Foundations.Data.Nat.Segment) | 2 | `h0 : f 0 = 0` | W1c2 | for k < f 0, segment f k = 0 (segment_pre_zero) and k < f 0 < f 1; otherwise segment_upper_bound' |
| 61 | `Nat.segment_upper_bound'` (Foundations.Data.Nat.Segment) | 3 | `h : f 0 ≤ k` | W1c2 | same: for k < f 0 use segment_pre_zero and k < f 0 < f 1 |
| 62 | `Cslib.ωSequence.cumLen_segment_zero` (Foundations.Data.OmegaSequence.Flatten) | 2 | `h_ls : ∀ (k : ℕ), 0 < (ls k).length` | W3c2 | for n below the first length, 0 is the only value of cumLen that is ≤ n, whatever the other lengths |
| 63 | `Cslib.ωSequence.drop_extract` (Foundations.Data.OmegaSequence.Init) | 5 | `h : k ≤ n - m` | W3c2 | if k > n - m both sides are empty |
| 64 | `Polynomial.monotone_eval` (Foundations.Data.Polynomial.Monotone) | 3 | `inst : IsOrderedRing R` | W3c2 | IsOrderedRing follows from CanonicallyOrderedAdd |
| 65 | `Polynomial.eval_mono` (Foundations.Data.Polynomial.Monotone) | 3 | `inst : IsOrderedRing R` | W3c2 | IsOrderedRing follows from CanonicallyOrderedAdd |
| 66 | `MeasureTheory.HasFiniteSupport.exists_eq_sum_smul_dirac` (Foundations.MeasureTheory.FiniteSupport) | 2 | `inst : MeasurableSingletonClass α` | W3c2 | shrink the finite support to a finite measurable set and split off minimal measurable neighbourhoods |
| 67 | `MeasureTheory.instHasFiniteSupportForallPiOfIsFiniteMeasure` (Foundations.MeasureTheory.FiniteSupport) | 6 | `inst : ∀ (i : ι), MeasureTheory.IsFiniteMeasure (μ i)` | W3c2 | a null cylinder has product measure 0 by the outer-measure bound, no σ-finiteness needed |
| 68 | `Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.narrow_aux` (Languages.LambdaCalculus.LocallyNameless.Fsub.Subtype) | 9 | `trans : ∀ (Γ : Cslib.LambdaCalculus.LocallyNameless.Fsub.Env Var) (σ τ : Cslib` | hypcheck-v111 |  |
| 69 | `Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.perm_env` (Languages.LambdaCalculus.LocallyNameless.Fsub.WellFormed) | 7 | `ok_Γ : Cslib.HasWellFormed.wf Γ` | W1c4 | NodupKeys transfers along the permutation |
| 70 | `Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.perm_env` (Languages.LambdaCalculus.LocallyNameless.Fsub.WellFormed) | 8 | `ok_Δ : Cslib.HasWellFormed.wf Δ` | W1c4 | NodupKeys transfers along the permutation |
| 71 | `Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.narrow` (Languages.LambdaCalculus.LocallyNameless.Fsub.WellFormed) | 9 | `ok : Cslib.HasWellFormed.wf (Γ ++ ⟨X, Cslib.LambdaCalculus.LocallyNameless.` | W1c4 | lookup of sub bindings is preserved without NodupKeys |
| 72 | `Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.narrow_cons` (Languages.LambdaCalculus.LocallyNameless.Fsub.WellFormed) | 8 | `ok : Cslib.HasWellFormed.wf (⟨X, Cslib.LambdaCalculus.LocallyNameless.Fsub.` | W1c4 | as for narrow, with Γ = [] |
| 73 | `Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.open_lc` (Languages.LambdaCalculus.LocallyNameless.Fsub.WellFormed) | 7 | `ok_Γ : Cslib.HasWellFormed.wf Γ` | W1c4 | pass to dedupKeys, which has the same lookups |
| 74 | `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.BetaAt.abs_close` (Languages.LambdaCalculus.LocallyNameless.Untyped.BetaAt) | 8 | `lc : M.LC` | W1c4 | closing then opening is opening then renaming; both preserve BetaAt without LC |
| 75 | `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_abs_close` (Languages.LambdaCalculus.LocallyNameless.Untyped.LeftmostReduction) | 7 | `lc : M.LC` | W2c2 | BetaAt.abs_close holds without LC, W1c4 ba14 |
| 76 | `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.steps_abs_cong` (Languages.LambdaCalculus.LocallyNameless.Untyped.LeftmostReduction) | 7 | `lc : M.abs.LC` | W2c2 | same proof with the LC-free steps_abs_close |
| 77 | `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Leftmost.normalization` (Languages.LambdaCalculus.LocallyNameless.Untyped.LeftmostReduction) | 5 | `lc : M.LC` | W2c2 | a non-LC term has no full-beta step, so N = M |
| 78 | `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.open_eq_app` (Languages.LambdaCalculus.LocallyNameless.Untyped.Properties) | 8 | `lc_m : m.LC` | W2c2 | n = app n1 n2; x ∉ fv m forces n1 = m, x ∉ fv n forces n2 = bvar 0 |
| 79 | `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.close_openRec_to_subst` (Languages.LambdaCalculus.LocallyNameless.Untyped.Properties) | 8 | `n_lc : n.LC` | W2c2 | opening inserts n without shifting; LC of m suffices |
| 80 | `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.close_open_to_subst` (Languages.LambdaCalculus.LocallyNameless.Untyped.Properties) | 7 | `n_lc : n.LC` | Probe2 | opening inserts n without shifting: (m.closeRec k x).openRec k n = m[x:=n] whenever LcAt k m, by structural induction |
| 81 | `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.app_l_cong_of_ne` (Languages.LambdaCalculus.LocallyNameless.Untyped.StandardReduction) | 7 | `hne : L ≠ L'` | W2c2 | if L = L' the empty sequence at index 0 meets the bound |
| 82 | `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.subst` (Languages.LambdaCalculus.LocallyNameless.Untyped.StandardReduction) | 10 | `lc_N : N.LC` | W2c2 | Standard.lc_l of hN gives N.LC |
| 83 | `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.subst` (Languages.LambdaCalculus.LocallyNameless.Untyped.StandardReduction) | 11 | `lc_N' : N'.LC` | W2c2 | Standard.lc_r of hN gives N'.LC |
| 84 | `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.of_beta_step` (Languages.LambdaCalculus.LocallyNameless.Untyped.StandardReduction) | 6 | `lc_M : M.LC` | W2c2 | FullBeta.step_lc_l gives M.LC |
| 85 | `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.abs_subst` (Languages.LambdaCalculus.LocallyNameless.Untyped.StandardReduction) | 9 | `lc_N : N.LC` | W2c2 | Standard.lc_l of hN gives N.LC |
| 86 | `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.abs_subst` (Languages.LambdaCalculus.LocallyNameless.Untyped.StandardReduction) | 10 | `lc_N' : N'.LC` | Probe2 | N'.LC follows from hN by Standard.lc_r |
| 87 | `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.abs_close` (Languages.LambdaCalculus.LocallyNameless.Untyped.StandardReduction) | 8 | `lc : M.LC` | W2c2 | BetaAt.abs_close holds without LC, W1c4 ba14 |
| 88 | `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.StandardSeq.abs_cong` (Languages.LambdaCalculus.LocallyNameless.Untyped.StandardReduction) | 7 | `lc : M.abs.LC` | W2c2 | same proof with the LC-free abs_close |
| 89 | `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_abs_app_multiApp` (Languages.LambdaCalculus.LocallyNameless.Untyped.StrongNorm) | 8 | `lc_N : N.LC` | Probe2 | if N is not LC the term is not LC, so it has no FullBeta step (step_lc_l) and is SN |
| 90 | `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_abs_app_multiApp` (Languages.LambdaCalculus.LocallyNameless.Untyped.StrongNorm) | 9 | `lc_MNPs : ((M.open' N).multiApp Ps).LC` | Probe2 | if (M^N) Ps is not LC then neither is (λM) N Ps (beta_lc, multiApp_lc), so it has no step and is SN |
| 91 | `Cslib.Logic.CLL.Proof.expand_onlyAtomicAxioms_dual` (private) (Logics.LinearLogic.CLL.EtaExpansion) | 2 | `a : Cslib.Logic.CLL.Proof.onlyAtomicAxioms a.expand = true` | W1c5 | instance of the public Proof.expand_onlyAtomicAxioms at a⫠ |
| 92 | `Cslib.Logic.Modal.Satisfies.four_trans` (Logics.Modal.Semantics) | 5 | `inst : Nonempty Atom` | W1c5 | without atoms the embedding e forces τ.B op empty, and then Trans holds vacuously |
| 93 | `Cslib.Logic.Modal.Satisfies.d_serial` (Logics.Modal.Unimodal.Basic) | 6 | `inst : Nonempty Atom` | W1c5 | instantiate D at ⊤: □⊤ → ◇⊤ yields a successor; no atom needed |
| 94 | `Cslib.Logic.Modal.Satisfies.l_induction` (Logics.Modal.Unimodal.Basic) | 7 | `inst : IsTrans World m.rel` | W1c5 | plain well-founded induction along the converse relation; transitivity unused |
| 95 | `Cslib.MachineLearning.PACLearning.hypothesisError_eq_add` (MachineLearning.PACLearning.Defs) | 5 | `hh : MeasurableSet h` | W3c5 | split along the measurable c: μ s = μ (s ∩ c) + μ (s \ c) |
| 96 | `Cslib.MachineLearning.PACLearning.hypothesisError_eq_add` (MachineLearning.PACLearning.Defs) | 6 | `hc : MeasurableSet c` | W3c5 | split along the measurable h: μ s = μ (s ∩ h) + μ (s \ h) |
| 97 | `Cslib.MachineLearning.PACLearning.error_map_eq_hypothesisError` (MachineLearning.PACLearning.Defs) | 5 | `hh : MeasurableSet h` | Probe2 | map ≥ preimage for any set (le_map_apply); ≤ via measurable cover toMeasurable(h∆c) ×ˢ univ ∪ cᶜ×{true} ∪ c×{false} |
| 98 | `Cslib.MachineLearning.PACLearning.empiricalError_eq_div` (MachineLearning.PACLearning.VersionSpace) | 8 | `hm : 0 < m` | W3c5 | m = 0: both sides are 0, as 0 / 0 = 0 in ℝ≥0∞ |
| 99 | `Cslib.MachineLearning.PACLearning.map_graph_eq_one` (private) (MachineLearning.PACLearning.VersionSpace) | 8 | `hG : MeasurableSet {p \| p.2 = c p.1}` | W3c5 | le_map_apply: map μ G ≥ μ (preimage G) = 1 for any set G |
| 100 | `Cslib.MachineLearning.PACLearning.pi_map_graph_eq_one` (private) (MachineLearning.PACLearning.VersionSpace) | 8 | `hG : MeasurableSet {p \| p.2 = c p.1}` | W3c5 | pi_pi holds for arbitrary sets; each factor is 1 by le_map_apply |
| 101 | `Cslib.MachineLearning.PACLearning.ae_mem_versionSpace_of_realizable` (MachineLearning.PACLearning.VersionSpace) | 10 | `inst : MeasureTheory.IsProbabilityMeasure P` | W3c5 | off-graph cylinders are null for the outer-measure product, no σ-finiteness needed |
| 102 | `Cslib.MachineLearning.PACLearning.versionSpaces_ncard_le` (MachineLearning.PACLearning.VersionSpaceLattice) | 3 | `hC : Set.Finite C` | W3c5 | an infinite class has infinitely many version spaces, so both sides degenerate: ncard = 0 |
| 103 | `Cslib.Probability.PMF.uniformOfFintype_apply` (Probability.PMF) | 2 | `inst : Nonempty α` | hypcheck-v111 |  |
| 104 | `Cslib.Probability.PMF.uniformOfFintype_map_equiv` (Probability.PMF) | 4 | `inst : Nonempty α` | W3c5 | Nonempty α from Nonempty γ via e.symm |
| 105 | `Cslib.Probability.PMF.uniformOfFintype_map_equiv` (Probability.PMF) | 5 | `inst : Nonempty γ` | W3c5 | Nonempty γ from Nonempty α via e |

## Pairs: joint removal (J1c0, 2026-11-11)

12 theorems have two removable hypotheses (the other 81 removable rows are the only removable hypothesis of their theorem). Each pair is decided by a kernel-checked proof in `checks/J1c0Hand.lean` (statements built by `drop2%`/`indep2%`, re-checked by `scripts/check_pairs.py`: definitional equality with the independently rebuilt `T''`, universes, standard axioms only); data in `results/removable_pairs.jsonl`.
Definition: for two non-dependent hypotheses `T''` is `T` without both; if they are dependent (the conclusion mentions them) `T''` is `∀ rest, Hᵢ ∧ Hⱼ`, i.e. both derivable from the binders that mention neither.

**7 jointly removable, 5 not.**

| Theorem | idx | Hypotheses | Verdict | Proof (`J1c0.`) | Why |
|---|---|---|---|---|---|
| `Nat.segment_zero` | 1, 2 | `hm : StrictMono f`, `h0 : f 0 = 0` | jointly removable | `segz12` | segment f 0 = 0 for every f |
| `Cslib.Automata.NA.FinAcc.nfa_single_start_accept_eq_regex` | 7, 8 | `hstart`, `haccept` | jointly removable | `nsaer78` | it is then `nfa_eq_regex` |
| `Cslib.Circuits.Shannon.exists_hard_function` | 2, 3 | `[Finite σ.Op]`, `[Finite U]` | jointly removable | `ehf23` | finite U: simulate by the binary full basis; infinite U: Nat.card U = 0, a constant needs a gate |
| `Cslib.FLP.FairScheduler.omega_forall_actions` | 10, 12 | `hd` (fairness), `hs0 : q s0` | jointly removable | `ofa1012` | neither is used |
| `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.sn_abs_app_multiApp` | 8, 9 | `lc_N`, `lc_MNPs` | jointly removable | `sn89` | LC term: both follow; non-LC term: no step, so SN |
| `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.abs_subst` | 9, 10 | `lc_N`, `lc_N'` | jointly removable | `sas910` | both from `hN` (`Standard.lc_l`, `lc_r`) |
| `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.Standard.subst` | 10, 11 | `lc_N`, `lc_N'` | jointly removable | `ss1011` | both from `hN` |
| `Cslib.Automata.DA.FinAcc.unique_minimal` | 3, 5 | `[Finite State]`, `hr : l.IsRegular` | **not** jointly | `um35` | l = {[n, n]} over ℕ, M = trie DFA on `List ℕ`: both `Nat.card` 0 (junk value), but states [0,1] ≠ [1,0] share a Nerode class, so no bijection |
| `Cslib.URM.evalState_toStandardForm_regs` | 2, 3 | `hp`, `hq` (dependent) | **not** jointly | `etsr23` | each from the other; p = [J 0 0 0] halts on neither side |
| `Cslib.Probability.PMF.uniformOfFintype_map_equiv` | 4, 5 | `[Nonempty α]`, `[Nonempty γ]` (dependent) | **not** jointly | `ume45` | each from the other via e; α = γ = Empty |
| `Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.Wf.perm_env` | 7, 8 | `ok_Γ`, `ok_Δ` | **not** jointly | `pe78` | Γ = [0 <: ⊤, 0 : ⊤], Δ = swap: `fvar 0` well-formed in Γ only (lookup finds the first binding) |
| `Cslib.MachineLearning.PACLearning.hypothesisError_eq_add` | 5, 6 | `MeasurableSet h`, `MeasurableSet c` | **not** jointly | `hea56` | Bool with σ-algebra {∅, univ}, P = dirac true, h = {true}, c = {false}: 1 = 1 + 1 |

Upstream consequence: for the 7 jointly removable pairs both hypotheses can go in one change; for the 5 others drop at most one (for `unique_minimal`, keep either `[Finite State]` or `hr`).
