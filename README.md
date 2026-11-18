# Redundant hypotheses in Lean projects

This repository provides tooling to decide, for every hypothesis of every theorem in a Lean project, whether it is
needed, and to prove the answer in Lean.

Each hypothesis gets one of these verdicts:

- **removable**: the theorem still holds without the hypothesis (Lean proof of the weakened statement `T'`);
- **necessary**: without it the theorem is false (Lean proof of `¬T'`, i.e. a counterexample);
- **independent** (less than 1% of cases): neither `T'` nor `¬T'` follows from Lean's axioms (for example due to opaque definitions).

Every removable and necessary verdict is backed by a stored kernel-checked Lean declaration using only standard axioms.

## Results

The analysis has been run on these libraries:

| Library | Version | Hypotheses | Necessary | Removable | Independent | Unresolved |
|---|---|---|---|---|---|---|
| [Lean 4 core](libs/core/Results.md) (`Init`, `Std`, `Lean`, `Lake`) | lean4 `a2ec8251` | 66,633 | 57,821 | 8,369 | 443 | 0 |
| Mathlib: [Data](libs/mathlib-data/Results.md), [Logic and Basic](libs/mathlib-logic-basic/Results.md) | Mathlib `bbff2954fe5` | 15,010 | 14,529 | 477 | 4 | 0 |
| [iris-lean](libs/iris-lean/Results.md) | `8293092f` | 6,260 | 6,035 | 195 | 5 | 25 |
| [CSLib](libs/cslib/Results.md) | `f8acdb37` | 2,699 | 2,593 | 105 | 1 | 0 |
| [combinatorial-games](libs/combinatorial-games/Results.md) | `e8c9538` | 2,597 | 2,392 | 146 | 0 | 59 |
| [Batteries](libs/batteries/Results.md) | `4af7237` | 1,326 | 1,259 | 66 | 1 | 0 |
| [SampCert](libs/sampcert/Results.md) | `a2c53bb` | 607 | 418 | 189 | 0 | 0 |

Private theorems are included (counted separately in each library's results). Each library's `Results.md` (under `libs/`) has the
breakdown by folder, the patterns among the removable hypotheses, the independent cases and the caveats; library
defects found along the way are in its `Findings.md`.

**Read the removable verdicts with care.** Each hypothesis is checked on its own: two individually removable
hypotheses of one theorem need not be removable together (joint removal was checked only for some pairs). Some
removable hypotheses are there by design (`proof_irrel`, `cast_eq`), and removing a hypothesis from a public lemma
breaks its callers.

## How

[`Methods.md`](Methods.md) describes the method in full. In short:

1. A mechanical tool (`HypCheck.lean`) tries cheap tactics on the theorem without the hypothesis, and searches small
   values plus hand-made law-violating models for a counterexample. Structural detectors find hypotheses the library's
   own proof never uses, instance hypotheses that type class resolution derives, and verdicts that follow from other
   verdicts (transitive necessity).
2. What remains goes to hand passes: AI agents (Claude Opus), one per cluster of related hypotheses, write Lean proofs
   of `T'` or `¬T'`. Agents never write results; every file is re-checked before it is merged.
3. Every hand, generated and structural proof file is checked by `check_hand.py` before it is merged: it compiles the
   file, compares each proved statement with `T'` / `¬T'` of the original theorem up to definitional equality, reports
   uncovered verdicts and rejects non-standard axioms. The tool's own proofs get the same statement check when they
   are found.

Of all 95,132 hypotheses, 54% were decided by the hand passes, 37% by the tool, the detectors and transitive necessity,
and 9% (almost all in Lean core) by a generated tactic for dependent hypotheses. The mechanical share ranges from 13.5%
(iris-lean) to 66% (Batteries). Removable hypotheses mostly needed the hand passes: 7,738 of the 9,547 (81%).

## Checking your own library

**Recommended:** clone this repository, open it in a coding agent such as Codex / Claude Code and say *"Do the hypothesis
analysis for &lt;library&gt; with hypcheck."* It builds the library, runs the mechanical checks below, and asks before longer
runs and before starting AI agents on what remains. Everything goes to `workspaces/<name>/`.

**Without AI (for mechanical checks):**

1. Build the library: `lake build` in its folder.
2. In this repository, run `tool/hypcheck /path/to/library RootModule` (for example `tool/hypcheck ../batteries Batteries`).
3. Open `workspaces/<name>/report.md`: it lists the hypotheses the theorems do not need, each with a Lean proof.

Step-by-step instructions, options and platforms: [`tool/README.md`](tool/README.md). On the libraries above, the
mechanical checks decided about 37% of all hypotheses (13.5% to 66% depending on the library), but only 19% of the
removable ones.

## Layout

| Path | What it is |
|---|---|
| `Methods.md` | The method: verdicts, how they are found, how proofs are stored and checked, caveats |
| `libs/<library>/` | One workspace per library: `Results.md`, `Findings.md`, `results/` (one JSON line per hypothesis), `checks/` (hand, chain and structural proofs), `proofs/tool/` (proofs found by the tool), `scripts/`, and an `AGENTS.md` with operational notes |
| `tool/` | The tool, for running the analysis on another library (`tool/README.md`) |
| `workspaces/` | Created by your own `tool/hypcheck` runs; ignored by git |
| `kit/` | Tool files shared by several workspaces, in the versions the results were made with (the workspaces hold symlinks to them) |
| `scripts/verify_rows.py` | Checks that every decided row points to an existing stored proof (no compilation) |

A results row names its theorem, the hypothesis index and name, the verdict, and where its proof is: `proofs_file`
(with the declaration in `proof`) or a `checks/…` file in `tactic`, relative to the workspace.

## Checking the proofs yourself

The proofs compile only against the exact library version in the table above, with that library's toolchain.

- **Lean core:** build lean4 at commit `a2ec8251` (`make -C build/release`) and set `LEAN4_DIR` to the checkout. Then,
  from `libs/core`, `scripts/recheck_proofs.sh` recompiles every stored proof file, and
  `scripts/check_hand.py FILE VERDICTS` checks one file's statements and axioms.
- **Other libraries:** check out the library at the given commit and build it (`lake exe cache get` first if it uses
  Mathlib, then `lake build`). Set its location: `HC_LIBDIR` in the workspace's `hc.env`, then `scripts/hclean
  --refresh`, or for Batteries and CSLib the environment variable `BATTERIES_DIR` or `CSLIB_DIR`. Then, from the
  workspace, `python3 scripts/recheck.py` builds the helper modules some proof files import and recompiles every
  stored proof file (`LANES=N` for parallel compiles), and `scripts/check_hand.py FILE VERDICTS` checks one file's
  statements and axioms. Each workspace's `AGENTS.md` lists its other commands.

All proof files of the core library were last recompiled together on 2026-11-07; later files were each checked when
they were merged, and a random sample was recompiled on 2026-11-15.

## License

Apache License 2.0 (`LICENSE`), the license of all the libraries analysed here. Material derived from a library stays
under that library's copyright: the module copies in `libs/core/proofs/reproof/` keep their original headers,
`libs/batteries/removals.patch` is a diff against Batteries, and some proofs are adapted from library proofs.
