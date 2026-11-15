#!/bin/bash
# scripts/swapcheck.sh CERT.lean: compile the certificate module and check it with SwapCheck
# (run from the repository root; uses the memory-capped runner scripts/lean.sh).
set -e
f=$1; m=$(basename "$f" .lean); d=certs/.olean
mkdir -p $d
LEAN_PATH=$d MEM=${MEM:-4G} scripts/lean.sh -o $d/$m.olean "$f"
MEM=${MEM:-4G} TMO=${TMO:-900} scripts/lean.sh --run scripts/SwapCheck.lean $d $m
