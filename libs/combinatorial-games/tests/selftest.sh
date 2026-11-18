#!/bin/bash
# Self-test of the agent pipeline (Header.lean -> scripts/verify.sh -> check_hand.py) on core-Lean theorems, so it
# runs in every workspace: 1 positive cluster (one necessary, one removable verdict) and 4 negative controls that
# must FAIL (wrong polarity, sorry, edited header, statement of another theorem). Writes only runs/selftest/ and
# checks/SelfTest*Hand.lean, never results/. Usage (from the workspace root): tests/selftest.sh
cd "$(dirname "$0")/.."
D=runs/selftest; mkdir -p $D
H=runs/probe/Header.lean
todo='{"theorem": "Nat.sub_add_cancel", "idx": 2}
{"theorem": "Nat.Simproc.le_add_ge", "idx": 3}'
nec='-- `Nat.sub_add_cancel` idx 2: necessary (n = 0, m = 1)
theorem st_nec : ¬ drop0% Nat.sub_add_cancel 2 := fun h => absurd (@h 0 1) (by decide)'
rem='-- `Nat.Simproc.le_add_ge` idx 3: removable (true for all a, b, c)
theorem st_rem : drop% Nat.Simproc.le_add_ge 3 := by intro a b c; simp only [eq_iff_iff]; omega'
mk() {  # mk NAME BODY VERDICTS [HEADER-SED]
  { cat $H; echo; echo "$2"; } > checks/$1Hand.lean
  [ -n "$4" ] && { sed "$4" checks/$1Hand.lean > checks/$1Hand.lean.tmp && mv checks/$1Hand.lean.tmp checks/$1Hand.lean; }
  echo "$todo" > $D/todo_$1.jsonl; echo "$3" > $D/$1_verdicts.jsonl
}
V_OK='{"theorem": "Nat.sub_add_cancel", "idx": 2, "status": "necessary"}
{"theorem": "Nat.Simproc.le_add_ge", "idx": 3, "status": "removable"}'
mk SelfTestPos "$nec
$rem" "$V_OK"
mk SelfTestPol "$nec
$rem" '{"theorem": "Nat.sub_add_cancel", "idx": 2, "status": "removable"}'
mk SelfTestSorry "$nec
-- \`Nat.Simproc.le_add_ge\` idx 3: removable
theorem st_rem : drop% Nat.Simproc.le_add_ge 3 := by sorry" "$V_OK"
mk SelfTestHdr "$nec
$rem" "$V_OK" 's/^-- hypcheck toolkit header/-- edited header/'
# wrong statement: the proof refutes Nat.le_antisymm idx 2, but comment and verdict claim Nat.sub_add_cancel idx 2
mk SelfTestWrong '-- `Nat.sub_add_cancel` idx 2: necessary
theorem st_wrong : ¬ drop0% Nat.le_antisymm 2 := fun h => absurd (@h 1 0 (by decide)) (by decide)' \
  '{"theorem": "Nat.sub_add_cancel", "idx": 2, "status": "necessary"}'
ok=1
for c in SelfTestPos SelfTestPol SelfTestSorry SelfTestHdr SelfTestWrong; do
  r=$(scripts/verify.sh $D $c 2>&1 | tail -1); echo "$r"
  if [ $c = SelfTestPos ]; then [[ $r == "VERIFY PASS"* ]] || ok=0; else [[ $r == "VERIFY FAIL"* ]] || ok=0; fi
done
(( ok )) && echo "SELFTEST OK" || { echo "SELFTEST FAILED"; exit 1; }
