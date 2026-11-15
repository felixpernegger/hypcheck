# Cluster-wave runbook (main session only)

Agents read `runs/waves/BRIEF.md` (+ `runs/probe/BRIEF.md`, `NOTES.md`). State and decisions live in the `Plan.md` Log.

## Before the first wave

1. User's go for the wave, with the cost model from P6a (PLAYBOOK §4): clusters × ~10 min + rows × rate, tokens = rows × tokens/row, wall = agent-min / 6.
2. `python3 scripts/cut_clusters.py plan 120` (add `--by stem` if lemmas repeat across wrapper types), then `python3 scripts/cut_clusters.py freeze 120`. Never re-freeze within a scope.
3. Cap the agent slice by available memory: `systemctl --user set-property --runtime @SLICE@ MemoryMax=<min(60% RAM, MemAvailable − 2.5 GB)> MemorySwapMax=0` (CSLib: 4.5–5 GB for 6 agents, peak 3.8 GB). Without systemd (`scripts/capped --backend` prints `none`) there is no slice cap: run fewer agents at once.
4. `python3 scripts/status.py --save`.

## Loop (rolling pool of ≤ 6 Opus agents)

1. **Start a cluster** when a slot is free: `python3 scripts/cut_clusters.py next <k>` (start a new wave number every ~6 clusters). Launch with the Agent tool, `model: "opus"`, in the background, with the prompt below; record the agent id in `runs/waves/W<k>/agents.txt` (SendMessage target).
2. **When an agent reports:** record its tokens (from the notification) in `runs/waves/tokens.json`; run `scripts/accept.sh runs/waves/W<k> <C>` in the background (verify → merge public + private → flow → totals; serialized by `runs/accept.lock`); copy its reusable helpers into `NOTES.md` (name, file:line, use) and its gave-up rows with obstruction into `TAILS.md`; refill the slot.
3. **After every ~6 clusters:** rates vs. model (agent-min ≈ fixed + rate × rows), decided and removable share, tokens vs. budget, memory peak (`memory.peak` of the slice), surprises, ETA. Log entry in `Plan.md`, short status to the user.
4. **Monitoring:** watch the slice's `memory.events` (`oom_kill`), MemAvailable < 3 GB, and clusters whose files stop changing for 20 min (Monitor tool, re-armed). If an agent's compiles keep getting killed, tell it (SendMessage) to split.
5. A cluster that ends with many rows open for lack of time gets a follow-up cluster with its remaining rows and pointers to its log and scratch dir. Gave-up rows with a shared obstruction become a tail cluster (`T<k>c<i>`: todo rows with `prior_obstruction`, emitted by hand into `runs/waves/T<k>/`).

## Prompt template

> You are a cluster agent for the hypcheck project on `@NAME@` (deciding whether each hypothesis of a library theorem is needed). Your cluster is `<C>` in `runs/waves/W<k>/`: <rows> open rows from <modules/stems> (<description from the .meta.json>). Up to five other agents run in parallel on other clusters.
>
> Read and follow `@WS@/runs/waves/BRIEF.md` exactly (it starts with `runs/probe/BRIEF.md`; read `runs/waves/NOTES.md` too), with `<C>` = `<C>`. Work in `@WS@`.
>
> Time box: stop starting new rows 60 minutes after your start, then run `scripts/verify.sh runs/waves/W<k> <C>` and give the short final report the brief asks for. Never merge, never edit files outside your own outputs and scratch dir.

## Pitfalls

- Never edit `accept.sh`/`verify.sh`/`flow.sh` while one runs (bash reads scripts incrementally): edit a copy and `mv` it in.
- Never wait on a process with `pgrep -f` on a pattern that occurs in your own command line.
- If flow keeps proposing a candidate that fails, `flow.sh` stops after that round; check `runs/flow/chain_<K>.log`.
