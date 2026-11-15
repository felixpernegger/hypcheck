# Brief for @NAME@ agents (probe P6a; the wave brief `runs/waves/BRIEF.md` extends it)

You get a todo list of open rows (theorem, hypothesis index) of the Lean library `@NAME@` (`@LIBDIR@`, modules `@MODULES@`). Decide as many as you can by hand within the time box and log every row honestly: the main session measures rates and re-plans from your log.

Everything happens in `@WS@`. The library is read-only: never edit it, never run git there. The other workspaces in `@KITDIR@/../libs/` and `@KITDIR@` are read-only too.

## The task

For each row (`theorem` `T`, `idx` `i`) of your todo file `runs/probe/todo_<C>.jsonl` (your cluster `C`, e.g. `Probe1`), prove one of:
- `T'` (T with that hypothesis dropped): **removable**, stated as `drop% T i`;
- `¬T'`: **necessary**, stated as `¬ drop0% T i`.

For a **dependent** row (`dependent: true`: later binders or the conclusion use the hypothesis) the verdict is about `∀ indep, Hᵢ`: removable = `indep% T i`, necessary = `¬ indep0% T i` (the full statement, which forces all other independent hypotheses to hold at your witness).

The rows carry the tool's `reason` for leaving them open (no values for a type, evaluation stuck, no counterexample among small values).

## Read first (≤ 10 minutes)

- `AGENTS.md` (constraints and pitfalls) and `@KITDIR@/PLAYBOOK.md` §1 (verdicts) and §3 (what makes agents effective).
- **Your toolkit: `runs/probe/Header.lean`. Copy it unchanged as the beginning of your output file.** It imports `@ROOT@` and provides `drop% T i`, `indep% T i`, `drop0%`/`indep0%` (universes set to 0: for refutations only). Example:
  ```lean
  -- `Nat.sub_add_cancel` idx 2: necessary (n = 0, m = 1)
  theorem p1_1 : ¬ drop0% Nat.sub_add_cancel 2 := fun h => absurd (@h 0 1) (by decide)
  -- `Nat.Simproc.le_add_ge` idx 3: removable (true for all a, b, c)
  theorem p1_2 : drop% Nat.Simproc.le_add_ge 3 := by intro a b c; simp only [eq_iff_iff]; omega
  ```
  Removable verdicts must keep universe polymorphism: use `drop%`/`indep%` and declare the theorem's universe variables. Private theorems are `_private.Mod.Path.«0».Name` in Lean terms, but `_private.Mod.Path.0.Name` (plain `0`) in the backticked comment.
- `scripts/models.txt` (and `scripts/models_@NAME@.txt` if it exists): models that refuted rows automatically.
- Library source under `@LIBDIR@` (path from each row's `module`).

## How to work

- Build a few reusable broken models first, prove once which laws they satisfy, then refute theorem by theorem. Give a model its own type so instance search fills remaining instances and `Decidable` instances.
- Removable verdicts are real findings: before proving one by hand, search the library (and its dependencies under `@LIBDIR@/.lake/packages/`) for a sibling lemma without the hypothesis.
- Instance hypotheses (`[Finite α]`, `[Nonempty α]`, `[LawfulMonad m]`, …): refute with a type or instance lacking the property, or show they are derivable or unused.
- For many rows of one shape, write a small generator (Python in your scratch dir).
- If a row resists for about 10 minutes, log it as `gave_up` with the exact obstruction and move on.

## Time box

Run `date` at the start (first log line `{"start": …}`). **Stop starting new rows 60 minutes after your start**, then run the checks and report.

## Output (only these files)

- `checks/<C>Hand.lean`: the header copy, then helpers inside `namespace <C> … end <C>`, then one declaration per verdict with short names (`<c>_<n>`). The comment block directly above each declaration names the original theorem in backticks; put **only theorem names** in backticks (`check_hand.py` treats every backticked dotted token as a candidate). Helper lemmas get comments without backticks.
- `runs/probe/<C>_verdicts.jsonl`: one line per decided row: the todo row plus `status` (`necessary`/`removable`), `note` (one line: the counterexample, or why removable), `dependent`/`derivable` as appropriate.
- `runs/probe/<C>_log.jsonl`: first line `{"start": …}`, last line `{"end": …}`, one line per todo row: `theorem`, `idx`, `outcome` (`necessary`/`removable`/`independent`/`gave_up`/`untouched`), `minutes`, `technique`, `obstruction` (for `gave_up`).
- `runs/probe/<C>_independent.jsonl`: only rows you can argue are independent of Lean's axioms (rare; field `independence` = `platform`/`opaque-fixpoint`/`opaque-constant`/`type-identity` or a new short kind with justification, `reason`, `independent_support`).
- Scratch files only in `runs/probe/scratch_<C>/`.

## Memory (shared with other agents)

- **Never run `lean`, `lake` or the lean-lsp MCP tools directly.** Use `scripts/lean.sh FILE.lean` (from `@WS@`): the library's Lean, ≤ 2.5 GB per call, all agents capped together, 15 min timeout (`TMO=120` for searches).
- At most one Lean process at a time; if a compile is killed, split it. Develop in small scratch files (header copy + attempt); compile the whole output file only near the end (full-file compiles share one lock, so a short wait is normal).

## Checks before you finish (required)

`scripts/verify.sh runs/probe <C>` must end with `VERIFY PASS <C>` (header unchanged, no `sorry`/`native_decide`/`axiom`/`implemented_by`/`opaque`/extra `import`, `check_hand.py` 0 Lean errors and 0 not covered, only standard axioms, no extra or duplicate rows). Run it once at the end. Leave out any verdict that fails a check and log it as `gave_up`.

**Never** edit the library, `results/`, `scripts/`, the header, other agents' files, `NOTES.md`, `AGENTS.md`, `CLAUDE.md`, `Methods.md`, `Results.md`, `Plan.md`, or the memory. Don't merge; the main session does that.

## Final report (≤ 20 lines; details belong in your log)

Start and end time; counts necessary / removable / independent / gave up / untouched; minutes per decided row; the removable rows with a one-line reason each; gave-up obstructions, grouped; reusable helpers worth adding to `NOTES.md` (name, file:line, use); the last line of `verify.sh`.
