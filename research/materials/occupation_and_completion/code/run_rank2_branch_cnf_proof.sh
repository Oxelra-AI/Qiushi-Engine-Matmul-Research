#!/usr/bin/env bash
# Generate a DIMACS/DRAT proof object for the T-level s=20 rank-2 A-factor branch
# under Wang dim<=3 occupation constraints. This is a support computation: if
# DRAT verifies UNSAT, it independently certifies the CP-SAT rank-2 branch result.
OUTDIR="data/wang_capacity_cnf_rank2"
mkdir -p "$OUTDIR"
CNF="$OUTDIR/t_s20_dim123_branch_rank2.cnf"
META="$OUTDIR/t_s20_dim123_branch_rank2.meta.json"
DRAT="$OUTDIR/t_s20_dim123_branch_rank2.drat"
CADLOG="$OUTDIR/t_s20_dim123_branch_rank2.cadical.log"
TRIMLOG="$OUTDIR/t_s20_dim123_branch_rank2.drat_trim.log"
STATUS="$OUTDIR/t_s20_dim123_branch_rank2.status.json"
python scripts/wang_capacity_cnf_branch.py \
  --branch-rank 2 --dims 1,2,3 --cnf "$CNF" --meta "$META"
GEN_EXIT=$?
if [ "$GEN_EXIT" -ne 0 ]; then
  printf '{"stage":"generate","exit_code":%d}\n' "$GEN_EXIT" > "$STATUS"
  exit "$GEN_EXIT"
fi
cadical --unsat --binary=false -n "$CNF" "$DRAT" > "$CADLOG" 2>&1
CAD_EXIT=$?
TRIM_EXIT=-1
if [ "$CAD_EXIT" -eq 20 ]; then
  drat-trim "$CNF" "$DRAT" > "$TRIMLOG" 2>&1
  TRIM_EXIT=$?
fi
python - <<PY
import json, pathlib
out=pathlib.Path('$STATUS')
payload={'stage':'complete','cadical_exit':$CAD_EXIT,'drat_trim_exit':$TRIM_EXIT,'cnf':'$CNF','meta':'$META','drat':'$DRAT','cadical_log':'$CADLOG','drat_trim_log':'$TRIMLOG'}
out.write_text(json.dumps(payload, indent=2)+'\n')
print(json.dumps(payload, indent=2))
PY
# Return success for UNSAT+verified; otherwise return solver code for inspection.
if [ "$CAD_EXIT" -eq 20 ] && [ "$TRIM_EXIT" -eq 0 ]; then
  exit 0
else
  exit "$CAD_EXIT"
fi
