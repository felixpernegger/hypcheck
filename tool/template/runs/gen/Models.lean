
/-! ## Library models for `refute_dep` (@NAME@)

Appended after `RefuteCore.lean` (which follows the agent header, so `@ROOT@` is imported). Add, for each
hypothesis shape that recurs among the dependent rows:
- a model and a lemma `¬ Law model` (prove the laws it does satisfy once, if premises need them), registered as
  a strategy: macro_rules | `(tactic| refute_strategy) => `(tactic| exact MyModel.notLaw)
- values the remaining binders need: macro_rules | `(refute_value) => `(MyModel.bad)
- closers for the premises: macro_rules | `(tactic| refute_closer) => `(tactic| norm_num)
Give each model its own type so instance search fills instance binders. Keep compiles cheap: every stored
`by refute_dep` proof reruns the search when the file is checked. Test on a pilot chunk first
(`scripts/gen_dep.py`), and use `REFUTE_DEBUG=1` to see which premise or binder blocks a row. -/
