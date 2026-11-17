# The hypcheck tool

`tool/hypcheck` checks every hypothesis of every theorem in a Lean 4 library and tells you which ones the theorem
does not need. Each answer comes with a Lean proof. No AI is involved.

## How to run it

**1. Install** elan (Lean's toolchain manager), Python 3 and git. Use Linux; for macOS and Windows see
[Platforms](#platforms).

**2. Download and build the library you want to check.** For example Batteries:

```bash
git clone https://github.com/leanprover-community/batteries.git
cd batteries
lake build
cd ..
```

If the library depends on Mathlib, run `lake exe cache get` before `lake build`.

**3. Download this repository and run the check:**

```bash
git clone https://github.com/felixpernegger/hypcheck.git
cd hypcheck
tool/hypcheck ../batteries Batteries
```

The first argument is the library's folder (the one containing `lakefile.toml` or `lakefile.lean`). The second is
its root module, the name you would `import`.

**4. Open the result:** `workspaces/batteries/report.md`.

The check prints its progress. Time grows with the size of the library (measured examples under
[What to expect](#what-to-expect)). To stop, press
Ctrl-C; to continue later, run the same command again.

## What the result means

`report.md` lists every hypothesis the theorem does not need, with the reason and the file that holds the proof.
Each hypothesis gets one of three answers:

- **removable**: the theorem is still true without it. A Lean proof of that is stored.
- **necessary**: without it the theorem is false. A Lean proof of that (a counterexample) is stored.
- **unresolved**: the tool could not decide.

Removable hypotheses are checked one at a time: two removable hypotheses of the same theorem may not be removable
together. Removing a hypothesis from a public lemma also changes every place that uses it.

All answers are also in `workspaces/<name>/results/public.jsonl`, one JSON line per hypothesis: `theorem`, `idx` (position
of the hypothesis among the theorem's arguments, counting from 0), `name`, `type`, `status`, `found_by` (which check
decided it) and the proof's location (`proofs_file` and `proof`, or `proof_file` and `proof_decl`).

## Checking a proof yourself

From the workspace folder, compile the proof file with the library:

```bash
cd workspaces/batteries
scripts/hclean checks/UnusedHand.lean
```

Exit code 0 with no `error:` lines means Lean accepted every proof in the file (warnings such as unused variables are harmless). To also check that each proof states exactly the claimed
answer and uses only the standard axioms: `python3 scripts/check_hand.py FILE.lean VERDICTS.jsonl`.

## Options

| Option | What it does |
|---|---|
| `--modules A,B` | Check only these parts of the library, e.g. `--modules Batteries.Data.List`. |
| `--private` | Also check private theorems. |
| `--inventory-only` | Set up and count the hypotheses, then stop. Run the same command without it to continue. |
| `--removable-only` | Only look for removable hypotheses. Much faster. |
| `--level fast` / `search` / `thorough` | How hard to look for proofs. Default `search`. `fast` is quicker; `thorough` searches deeper and is slower. |
| `--olean-level auto` / `private` / `server` | How the checker loads the library. `auto` (default) picks `server` for libraries that use the module system: much less memory, but no proof repair. |
| `--no-exact` | Leave the slow library search `exact?` out. Faster, about half the memory per worker. |
| `--workers N` | Number of parallel processes. Default: chosen from your CPU count and free memory. |
| `--name NAME` | Workspace name. Default: the library folder's name in lower case. |
| `--workspace DIR` | Where to put the results. Default `workspaces/<name>` in this repository (ignored by git). |

## What to expect

- **Time:** `--modules Batteries.Data.List` (338 hypotheses) took 5 minutes with 3 workers, plus about 1 minute to
  build the tools; 487 hypotheses from iris-lean took 7 minutes with 4 workers.
- **Disk:** about 3 GB per library, for tools built with the library's Lean version.
- **Unresolved answers:** how many the tool decides depends on the library. In the published results it decided
  37% overall, from 13.5% (iris-lean) to 66% (Batteries); most of the rest came from AI agents (see the end). It
  finds necessary hypotheses much more often than removable ones: of the 9,401 removable hypotheses in the published
  results, it found 19%.

## Checking one theorem

After a first run (or `--inventory-only`):

```bash
cd workspaces/<name>
scripts/hcrun hypcheck --module Batteries --ns List.Sublist.erase_diff_erase_sublist --level search
```

This prints one JSON line per hypothesis of that theorem and stores nothing. Here it reports that hypothesis `x`
(`l₁.Sublist l₂`) is removable, proved by `exact?`. A line `PANIC at String.Slice.pos!` may appear before it: it
comes from Lean's `exact?` and is harmless. All options are listed at the top of
`template/scripts/HypCheck.lean`.

## Platforms

| System | Works? |
|---|---|
| Linux | Yes, tested (Ubuntu 24.04). |
| Linux without systemd (e.g. Docker) | Yes, tested, but without the memory limit (see below). |
| macOS | Not tested. Would run without the memory limit. |
| Windows 11 | Not directly. Install WSL2 (`wsl --install` in an administrator terminal, then restart), open Ubuntu, and follow the Linux steps there. Keep the files in the Linux home folder (`~/`), not under `/mnt/c`. Not tested. |

**Memory limit.** On Linux with systemd, the tool runs Lean inside a memory limit, so if it needs too much memory one
process is stopped instead of the whole computer freezing. Without systemd there is no limit and the tool prints a
warning. Then use fewer workers (`--workers 2`) on a machine with little memory. Settings: `HC_CAP=none` turns the
limit off and silences the warning; `MEM_MAX=4G` sets the limit's size.

## Full analysis with AI agents

The published results also decided the unresolved hypotheses, using AI agents that write the missing Lean proofs.
To do that for a library, open this repository in a coding agent such as Claude Code and say:

> Do the hypothesis analysis for &lt;library&gt; with hypcheck.

The agent follows [NEW_LIBRARY.md](NEW_LIBRARY.md): it builds the library, runs `tool/hypcheck` as above, and then asks before starting AI agents on the unresolved hypotheses, since they cost money. Their results go to the same workspace.

## Running the steps by hand

`tool/hypcheck` runs these scripts inside the workspace. Each can also be run on its own from the workspace folder:

| Step | Command |
|---|---|
| create workspace (from the repository root) | `tool/new_target.sh NAME LIBDIR ROOT [MODULES] [WORKSPACE]` (default `workspaces/NAME`) |
| list all hypotheses | `scripts/inventory.sh` |
| hypotheses the library's proof never uses | `scripts/struct.sh`, then `scripts/struct_proofs.sh` |
| tactic search and counterexamples | `scripts/run.sh N OUT.jsonl [HypCheck options]`, then `python3 scripts/merge_tool.py OUT.jsonl TAG` and `python3 scripts/repair_proofs.py K OUT.jsonl` |
| answers that follow from other answers | `scripts/flow.sh` |
| report | `python3 scripts/report.py report.md` |

The method in detail, with measured rates: [PLAYBOOK.md](PLAYBOOK.md). Changing the tool: [AGENTS.md](AGENTS.md).
