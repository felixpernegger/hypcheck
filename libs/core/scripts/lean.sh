#!/bin/bash
# Memory-capped stage1 Lean: each call runs in its own systemd scope with MemoryMax=${MEM:-2500M}, no swap,
# and a ${TMO:-900} s timeout, so a runaway elaboration is killed instead of freezing the machine.
# The environment (e.g. LEAN_PATH) is passed through. Override the binary with LEAN=/path/to/lean.
# Usage (from the repository root): scripts/lean.sh [lean args] FILE.lean
L=${LEAN:-${LEAN4_DIR:?set LEAN4_DIR to a lean4 checkout built at commit a2ec8251 (see README.md)}/build/release/stage1/bin/lean}
exec systemd-run --user --scope --quiet -p MemoryMax=${MEM:-2500M} -p MemorySwapMax=0 \
  timeout ${TMO:-900} "$L" "$@"
