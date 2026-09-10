# Execution Status

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Completed this ARTIFACT:
1. **Repaired separator**: Fixed syntax-breaking code insertion in `witness_subset_separation.py` where `validate_and_reencode_learned_record` was inserted inside `full_lut_violations`. Both functions now correctly separated.
2. **Hardened verifier**: Rewrote `verify_witness_subset_cnf.py` (schema v2) with structural consistency checks: prefix/candidate disjointness, target=20-|prefix|, survivor⊆candidates, vertex_excluded=candidates\survivors, edge point distinctness, DRAT return code 0 + VERIFIED.
3. **Smoke test idx25**: 5 rounds UNSAT, DRAT verified, structure_ok=true, exact_sequence_match=true.
4. **Multi-witness enhancement**: Modified witness-subset path to learn ALL C(selected_in_row, r+1) subsets from model's selection, not just one. Tested on rep2: 94K learned clauses in 5 rounds (vs ~2.4K for single-witness).
5. **Rep2 orbit analysis**: Stab({E11,E12}) has order 192, creates 17 orbits on 509 candidates (sizes 1-96). 5 generators computed. Base graph has α≥18 (all rank-1 greedy IS). Full-LUT violations: 3,441 for greedy IS.
6. **Proof chain architecture**: Saved in workspace/notes/proof_chain_architecture.md.

## Background tasks launched:
- s33_t20_tool1: k=6 remaining (idx 26,27,29,30,31) - 80 rounds, 5400s timeout
- s33_t21_tool1: k=5 all 10 (idx 12-21) - 80 rounds, 7200s timeout
- s33_t22_tool1: k=4 all 7 (idx 5-11) - 80 rounds, 7200s timeout
- s33_t23_tool1: k=1,2,3 all 5 (idx 0-4) - 80 rounds, 7200s timeout
- s33_t24_tool1: rep2 - 120 rounds, 10800s timeout

## Current batch status (as of last check):
- k=6 idx26: round 44, 236K clauses (still iterating)
- k=5 idx12: CLOSED (UNSAT, 4 rounds, DRAT verified)
- k=5 idx13: SOLVER_UNKNOWN (round 27, 156K clauses, CaDiCaL timed out)
- k=5 idx14: CLOSED (UNSAT, 4 rounds, DRAT verified)  
- k=5 idx15: round 2 (just started)
- k=4 idx5: round 42, 350K clauses (still iterating)
- k=1 idx0: round 48, 292K clauses (still iterating)
- rep2: round 53, 129K clauses (still iterating)

## Key concerns:
1. **SOLVER_UNKNOWN**: idx13 (k=5, 265 survivors, target 15) hit CaDiCaL timeout at 300s. Need to re-run with longer solve timeout or different solver settings.
2. **Slow convergence**: Several strata at 40+ rounds without UNSAT. May need 200+ rounds or the multi-witness approach.
3. **Rep2**: Violations oscillate 1.5K-3.8K in pilot; production run at round 53 with 129K clauses still running. May need multi-witness + symmetry breaking.

## Next work:
1. Collect batch results and verify closed strata
2. Re-run SOLVER_UNKNOWN cases with longer timeout and/or multi-witness
3. For strata that don't close in 80 rounds: launch longer runs with multi-witness
4. For rep2: if production run doesn't close, build symmetry-breaking enhanced version
5. Build unified proof manifest binding all closed strata with their artifacts
