# Methods

How each hypothesis gets its verdict, how the verdicts are proved, and how the proofs are checked. This applies to
every library in `libs/`; library-specific additions (extra models, toolchains) are in that library's `Results.md`.

## What is checked

For every theorem of the selected modules that has a source position (so compiler-generated lemmas such as
`match_1.congr_eq_*` are left out) and at least one Prop-valued parameter, every such parameter is checked on its own.
This includes all binder kinds: `(h : p)`, `{h : p}` and Prop-valued instances such as `[NeZero n]` or `[LawfulBEq α]`.
Private theorems are checked too, but counted separately (`private.jsonl`).

## Verdicts

Let `T : ∀ xs, C` be a theorem, `hᵢ : Hᵢ` one of its Prop parameters, and `T'` the statement `T` without `hᵢ`.
Exactly one of `T'` and `¬T'` holds classically. Each hypothesis gets one of these verdicts:

| Verdict | Meaning | What is proved in Lean |
|---|---|---|
| **removable** | the theorem stays true without the hypothesis | `T'` |
| **necessary** | dropping the hypothesis makes the theorem false | `¬T'` (a counterexample) |
| **independent** | neither `T'` nor `¬T'` follows from Lean's axioms | depends on the kind, see below |
| **unresolved** | not decided | nothing |

**Dependent hypotheses.** If `hᵢ` occurs later in the statement (an index bound in `l[i]'h`, a proof in `⟨i, h⟩`),
it cannot simply be deleted. It is still unneeded if it follows from the parameters that do not depend on it (`indep`):
then it can be replaced by a derived proof, and by proof irrelevance the statement means the same thing.
- removable: a proof of `∀ indep, Hᵢ` (plus the restated theorem with `hᵢ` replaced by the derived proof);
- necessary: a proof of `¬ ∀ indep, Hᵢ`, i.e. values where all other hypotheses hold and `Hᵢ` fails.

Some removable dependent hypotheses are the subject of the lemma itself (`proof_irrel`, `cast_eq`, `Subtype.eta`,
`Fin.eta`): removable in the technical sense, but not something to change.

**Independent hypotheses** arise where the statement turns on something the axioms leave open. The field
`independence` gives the kind, `independence_evidence` what is proved in Lean, `reason` the argument:
- `platform`: `System.Platform.numBits` is opaque, known only to be 32 or 64. Both halves are proved
  (`numBits = 32 → T'` and `numBits = 64 → ¬T'`, or the other way round). All 183 such rows in the core library also
  carry a formal certificate (below), marked `provably_independent`.
- `opaque-fixpoint`: both sides of the statement are values of an opaque fixpoint (iterator consumers without a
  `Finite`/`Productive` instance) with no structural link. Lean proves a support lemma (a value assignment that gives
  `¬T'`); that `T'` is consistent is a model argument.
- `type-identity`: refuting `T'` would need a provable disequality of types such as `List β ≠ Array β`, which Lean
  cannot prove. Argument only.
- `opaque-constant`: an equation between `opaque` families that no axiom fixes (three Lake rows). Argument only.

### Swap certificates (formal independence)

An `opaque` constant `c` is a black box to the kernel. Replacing it by a definition `c := v` only adds a reduction
rule, so every proof that checks before still checks after, and the new environment is consistent if the old one is.
Hence a kernel-checked proof of `¬T'` with `c := v₂` shows that `T'` is unprovable, and one of `T'` with `c := v₁`
shows that `¬T'` is unprovable: `T'` is independent (relative to `propext`, `Classical.choice`, `Quot.sound`).

`libs/core/scripts/SwapCheck.lean` checks such certificates: a certificate states the swap as an axiom `@c = v`, the
checker replays the dependency closure of its theorems through the kernel into an empty environment with `c`
replaced by the definition, and rejects any other axiom, unsafe constant, non-opaque target or double swap. Library
axioms whose statements depend on the swapped constant must be re-proved by the certificate. The 183 platform rows of
the core library are certified this way (`libs/core/certs/platform/`); test certificates, including five that must be
rejected, are in `libs/core/certs/test/`.

## How verdicts are found

### 1. The mechanical tool (`HypCheck.lean`)

One fresh Lean session per theorem; every goal is built as a closed term and proved in an empty local context, so a
tactic can never see the dropped hypothesis.

**Removal.** A list of cheap tactics (`omega`, `simp_all`, `grind`, combinations, `contradiction`, each with a
heartbeat limit) tries to prove `∀ rest, ¬Hᵢ → C`; the proof of `T'` then splits on `Hᵢ` (`Classical.byCases`).
If the same tactics also prove `∀ rest, Hᵢ`, the verdict is marked `derivable`.

**Counterexample search.** The data variables get small values, and the tool proves
`¬(∀ remaining hypotheses, C)` at those values with `decide`, `decide +kernel`, `simp`, `omega` and similar.
- Values per type, smallest first: `Nat` 0–10 and a few larger, `Int` small positive and negative numbers, `Bool`,
  `Prop`, `BitVec`, `Fin n`, `Char`, `String`, lists/arrays/options/vectors built from small elements, `UInt*`/`Int*`,
  plain structures, simple functions, and `Nat`/`Bool` for type variables. Every number occurring in the statement is
  tried with its neighbours.
- **Hand-made models** (`scripts/models.txt`): bad instances that violate exactly one law, written once and reused
  everywhere their type fits, e.g. a `BEq Nat` that is an equivalence but not lawful, a non-associative `Min`, a
  preorder that is not antisymmetric, a monad that counts binds. Kept class hypotheses that the model does satisfy are
  proved field by field.
- An equation hypothesis `x = t` fixes `x := t` instead of enumerating `x`.
- Combinations are tried in order of increasing size, with limits on count and time.

**Structural detectors** (fast, no search):
- *unused*: the library's own proof term does not mention `hᵢ`; the stored proof is that term with the binder dropped
  (`drop_unused% T i`);
- *transitively unused*: `hᵢ` is only passed on to other theorems at positions that are themselves unused;
- *instance derivable*: type class resolution finds the instance from the other binders;
- *reproof*: the library module recompiled with the theorem's own proof minus the binder;
- *proof repair* (`tool/`, HypCheck v12; used for SampCert): the library proof with every use of `hᵢ` rebuilt by cheap tactics;
- *transitive necessity*: if `B`'s proof passes its hypothesis `hⱼ` only to `A`'s hypothesis `hᵢ`, then `A' → B'`, so a
  proof of `¬B'` gives `¬A'`; *twins*: identical statements share their verdict. These rounds are repeated after
  every merge ("flow") until nothing new follows.

### 2. Generated tactics

For large families of similar dependent hypotheses, a generated search tactic does the counterexample search inside
Lean: `refute_dep` (core, Std) unifies the hypothesis with a stock of law-violating models and ill-formed literals
(trees with a wrong size field, hash maps without buckets) and backtracks over the remaining binders. Every proof is a
`theorem … : ¬ … := by refute_dep` whose file defines the tactic, so the file is self-contained.

### 3. Hand proofs, written by AI agents

What the tool cannot decide goes to hand passes: one AI agent (Claude Opus) per cluster of related hypotheses writes
Lean proofs of `T'` or `¬T'`. The pattern that worked: build a few reusable broken instances first, each violating
exactly one law, prove the laws they satisfy once, then refute theorem by theorem; for many lemmas of the same shape,
generate the declarations from a template. Statements are read from the library with elaborators (`drop% T i` for
`T'`, `indep% T i` for `∀ indep, Hᵢ`, `drop0%`/`indep0%` with universes set to 0 for refutations), not retyped.

The *main session* is the coordinating session: it runs the tools, cuts the open hypotheses into clusters, briefs the
agents, and re-checks and merges their files. Agents run in *waves* (a pool of up to six at a time, a new cluster
whenever one finishes). Agents never write to the results. Every agent file is re-checked before its verdicts are
merged (next section).

Techniques that decided whole families are described in the hand files themselves; examples:
- *non-finite iterators* (`LP` skips to itself, `YL` yields forever) for dropped `Finite`/`Productive` instances;
- the *two-loop trick*: instantiate `T'` twice with two different vacuously lawful loops, so that an opaque side stays
  the same while the other side changes;
- *ill-formed literals* (a tree whose size field is 0, a hash map key in the wrong bucket) for dropped `WF` hypotheses;
- type-synonym models (`def NF := Nat` with its own instances), so that instance search fills the remaining arguments.

## Stored proofs and how they are checked

Every removable and necessary verdict has a Lean declaration in the repository:
- tool verdicts: `proofs/tool/<run>/…`, declaration `HypCheckProof.T.h<i>` (field `proof`), rendered from the tactic
  and witness values and re-elaborated with a statement check right after the verdict; the field `proofs_file` of the
  row names the folder;
- hand, generated and structural verdicts: `checks/*.lean`, named in the row's `tactic` field.

Before a hand file is merged, `check_hand.py`
1. compiles it in a fresh process;
2. checks that each declaration's statement is definitionally equal to `T'`, `¬T'` or `¬ ∀ indep, Hᵢ` of the original
   theorem, built from the library constant (a removable proof must keep the theorem's universe parameters);
3. reports verdicts the file does not cover;
4. checks the axioms: only `propext`, `Classical.choice` and `Quot.sound` are accepted, so no `sorry`,
   `native_decide` or custom axioms.

Private theorems cannot be referenced from another module, so their proofs are compiled per module with that module
as the file's main module (`bymod/`).

## Caveats

- Each hypothesis is checked **on its own**. Two individually removable hypotheses of one theorem may not be removable
  together; joint removal was checked only for some pairs (`removable_pairs.jsonl` where present).
- Removing a hypothesis from a public lemma breaks its callers; a change upstream needs a deprecated alias or a new
  name.
- For a dependent hypothesis, `check_hand.py` also accepts a refutation of the narrower statement in which only the
  binders that `Hᵢ` mentions are kept. Hand passes were told to state the full `indep% T i`, but how many merged rows
  rest on the narrow form alone was not audited.
- `type-identity`, `opaque-constant` and the consistency half of `opaque-fixpoint` rest on arguments, not on Lean proofs.
