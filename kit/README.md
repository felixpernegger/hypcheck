# Shared kit files

Every file here is shared by at least two library workspaces under `libs/` (all but `scripts/recheck.py`, which was
added for readers, were byte-identical copies there). Each of those workspaces holds a
relative symlink to it at the same path (`scripts/…`, `scripts/priv/…`, `tests/selftest.sh`), so every workspace stays
runnable on its own: the scripts locate their workspace from the symlink's path (`os.path.abspath(__file__)`,
`dirname "$0"`; neither resolves symlinks), and files that differ between workspaces stay real files there.

A workspace without a symlink for a file has its own version. Examples: `libs/iris-lean` keeps an older
`HypCheck.lean`; `derive_proofs.py`, `lean.sh` and the lock file `big.lock` are kept per workspace (two `lean.sh`
variants; `derive_proofs.py` here would clash with the core version; a shared lock file would serialise compiles across
workspaces).

Most files come from the tool's workspace template (`tool/template/`); the copies here are the versions the workspaces
were run with, which may be older than the current tool. **Editing a file here changes it for every workspace that links
to it** (`find libs -lname '*kit/<path>'` lists them).
