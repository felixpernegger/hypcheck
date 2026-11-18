# Methods (combinatorial-games)

Everything not listed here follows `../../Methods.md` and `../../tool/PLAYBOOK.md` (verdicts, phases, soundness,
agent practice). This file records what differs for `combinatorial-games`.

## Tool and setup

- **HypCheck v12.3** (`scripts/HypCheck.lean`; the tool changes were made for this library and are in `../../tool/`):
  - universe-level renderings of stored proofs;
  - renderings without the library's delaborators. `delabOfSets` prints `OfSets.ofSets (Player.cases s t) h` as
    `!{s | t}`, which drops the proof argument, so 6 removable proofs failed to re-elaborate until this was added;
  - `--extra-tacs FILE` for library tactics: `scripts/tactics_combinatorial-games.txt` adds the library's decision
    procedure `game_cmp` to the counterexample and premise tactics;
  - `--olean-level`, slim imports and `--no-exact`, recovered from earlier work.
- **Module system.** The library is written as Lean modules.
  - Public rows ran at olean level `server`: no proof bodies are loaded, which uses less memory but means no proof
    repair. Re-pilot: same 22/100 verdicts as the old non-module pilot, peak 2.7 GB vs 4.1 GB for 3 workers.
  - Private rows need level `private`, about 2.2 GB per worker; 6 workers exceeded the cap, so private reruns used 2.
  - The agent header `runs/probe/Header.lean` is a module (`module`, `public import HCHeaderM`, `import HCRefute`,
    `import all` of every library module, no `public section`). The `refute_dep` core is compiled as the module
    `HCRefute` with `meta` definitions. Header modules live in `tools/hcrepair` (add it to `HC_EXTRA_PATH`).
- **Models:** `scripts/models_combinatorial-games.txt` (small games, surreals, nimbers, ordinals).
- **Memory:** 15 GB laptop, agent slice capped at 9 GB (≤ 60% RAM) for 6 agents; the slice peaked at 3.75 GB during
  the waves.
  - An agent's uncapped Python search once reached 7 GB and crashed the editor. Since then the agent brief requires
    every non-Lean program to run under `scripts/capped --mem 1500M`.
  - Per-process cap kills afterwards stayed contained: 6 kills, all from heavy `game_cmp` attempts.

## Agent techniques that recur here

- **Games as counterexamples, checked by `game_cmp`.** Small explicit games (`!{{…} | {…}}`) refute most `Numeric`,
  `Short`, `Impartial` and comparison hypotheses. Python game calculators (agent scratch, not published) found the candidates first.
- **Split heavy products.** One `game_cmp` on a whole statement with products times out or runs out of memory.
  Instead, prove each product separately as `p * q ≈ g` for a small explicit game g, option by option with
  `equiv_of_exists` + `mulOption_mem_moves_mul` when needed (template `checks/T2c0Hand.lean` `d6`), then combine in
  `Game` with `abel`. `Game.mk` of a product of up to three factors can be rearranged freely; with four factors,
  top-level associativity and commutativity keep the pairing.
- **Universe tricks for `Small` rows.** At universe 0 every `Small` instance holds, so `drop0%`/`indep0%` make these
  rows trivially true. Agents state them by hand at universe 1 (`dropU%`/`indepU%` elaborators in
  `checks/W1c3Hand.lean`), with `Set.univ` of a large type as the witness.
- **Reusable models** (in the `checks/` files named):
  - games: W = {↑|} ≈ 1 non-numeric and Y = {-1,0|} (`W3c2Hand.lean`, `T1c1Hand.lean`), Z0 = {∅|2}
    (`W3c1Hand.lean`), XP = {±1|} and XH (`T1c1Hand.lean`), the library's ⋆′;
  - cuts: the non-Small cut `X` (`W2c4Hand.lean`);
  - nimbers: F4/F16 arithmetic (`W2c1Hand.lean`, `T3c2Hand.lean`), T = algClosure 0, R = ∗(T^ω) and the Laurent
    ring X1 (`T1c0Hand.lean`), and `mainY` (`T2c1Hand.lean`).
- **Private lemmas:** `priv%` with `show` (no `rw` on private definitions); `attribute [local semireducible] LGame`
  for the private corecursor.

## Limits met

- **Inverses of numeric games with a positive option have infinitely many options.** No product with such an
  inverse can be evaluated, which blocks the remaining division rows.
- **Agent helper lemmas cannot be reused by the tool under the module system.** Hand files compile as modules
  (`scripts/hand_modules.py`, patched for module headers), but their declarations are private, and a
  `public section` fails in 24 of 28 files because the proofs use library-private lemmas. The reuse rerun (Step 0)
  therefore only added the agents' games as models, and decided nothing.
