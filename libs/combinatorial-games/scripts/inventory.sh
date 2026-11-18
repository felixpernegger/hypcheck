#!/bin/bash
# P1 inventory: PropParams over the library (public and private), rows files, report.
# Usage (from the workspace root): scripts/inventory.sh        -> runs/inventory/{pp,rows}_{public,private}.jsonl, report.txt
set -e
source hc.env
HC_CAP=$(scripts/capped --backend) || exit 1; export HC_CAP  # detect (and warn) once
mkdir -p runs/inventory
imp=(); for m in ${HC_ROOT//,/ }; do imp+=(--import "$m"); done
for kind in public private; do
  extra=(); [[ $kind == private ]] && extra=(--only-private)
  MEM=${MEM:-4G} scripts/measure.sh runs/inventory/pp_$kind -- scripts/hcrun propparams "${imp[@]}" --all-params "${extra[@]}" \
    -o runs/inventory/pp_$kind.jsonl
  python3 scripts/make_rows.py runs/inventory/pp_$kind.jsonl runs/inventory/rows_$kind.jsonl
done
python3 scripts/inventory.py runs/inventory/pp_public.jsonl runs/inventory/pp_private.jsonl | tee runs/inventory/report.txt
