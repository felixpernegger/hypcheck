# Results (@NAME@)

Analysed version: `@LIBDIR@` at commit `<fill in: git -C @LIBDIR@ log -1 --format='%h %cs'>`, toolchain `@TOOLCHAIN@`. If the checkout moves, rebuild and re-check before merging new runs.

Scope: all theorems with at least one Prop-valued parameter in modules `@MODULES@`, public and private counted separately; compiler-generated lemmas without source position excluded.

## Inventory

(P1: rows, dependent and instance shares, per folder.)

## Run history

(One entry per phase: what ran, measured cost, verdicts merged, `found_by` tags.)

## State

| | Necessary | Removable | Independent | Unresolved | Rows |
|---|---|---|---|---|---|
| public | | | | | |
| private | | | | | |

## Caveats

Each hypothesis is checked on its own (joint removal only for the pairs decided in P7); "unresolved" says nothing either way; removing a hypothesis from a public lemma breaks callers.
