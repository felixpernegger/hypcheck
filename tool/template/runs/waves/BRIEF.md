# Brief for @NAME@ cluster agents (P6b, waves W1…)

**Read `runs/probe/BRIEF.md` first and follow it**, with these changes:

- Your cluster is `<C>` = `W<k>c<i>` (or `T<k>c<i>` for a tail cluster) in wave directory `runs/waves/W<k>/` (resp. `T<k>/`): todo `todo_<C>.jsonl`, outputs `<C>_verdicts.jsonl`, `<C>_log.jsonl`, optional `<C>_independent.jsonl` there, scratch dir `scratch_<C>/` (already created), proof file `checks/<C>Hand.lean`.
- A cluster is all open rows (~120) of a run of neighbouring modules (or of whole lemma stems), so rows share definitions and models: work in file order, but do rows with `unlocks` > 0 early (a necessary verdict there decides that many further rows automatically).
- **Read `runs/waves/NOTES.md` before starting:** reusable models, helpers and arguments from earlier agents, with file:line. Copy what you need into your own `namespace <C>`; never import other hand files.
- Tail clusters: every row resisted an earlier agent; its `prior_obstruction` field and the leads in your prompt say why. Time box 75 minutes instead of 60.
- Check with `scripts/verify.sh runs/waves/W<k> <C>` (must end with `VERIFY PASS <C>`).
- In the final report, list helpers worth sharing as `name (checks/<C>Hand.lean:line): use`, so the main session can copy them into `NOTES.md`.
