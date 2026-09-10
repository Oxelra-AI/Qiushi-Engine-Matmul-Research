# Construction Pipeline and Enhanced Trace Filter

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Key Results

### Swap Search for n=22 Wang-admissible A-multisets
- Wang occupation at n=22 is very loose: hill-climb from deletion seeds converges in 2-4 swaps (~6s)
- ALL 6 deletion seeds (3 independent GL3 classes) converged to zero violations
- Random seeds converge less often: ~2/10 reach 0 violations in 10-14 iters

### Three-level Filtering Pipeline
1. **Wang occupation** (necessary A-side): trivially satisfiable at n=22
2. **Basic trace filter** (tight-contraction trace eqs): rejects random Wang-admissible candidates
3. **Enhanced trace filter** (+ nullspace conditions): rejects deletion-seeded candidates 
4. **Fixed-A Brent completion** (exact B/C SAT): final test, catches all remaining

### Results by candidate source:

| Candidate | Wang | Basic Trace | Enhanced Trace | Brent |
|-----------|------|-------------|----------------|-------|
| Deletion class 1 (flip_del384) | PASS | PASS [819,819] | FAIL [1365,1366] | UNSAT 6.3s |
| Deletion class 2 (flip_del268) | PASS | PASS [787,787] | PASS [921,921] | UNSAT 7.6s |
| Deletion class 3 (flip_del392) | PASS | PASS [816,816] | FAIL [1396,1397] | UNSAT 81s |
| Random_42_3 | PASS | FAIL (21 tight) | — | — |
| Random_42_5 | PASS | FAIL (20 tight) | — | — |
| Known rank-23 control (n=23) | PASS | PASS [792,792] | PASS [1325,1325] | SAT 4.07s ✓ |

### Enhanced Filter Mathematics

For tight contraction M_lambda with rank r and |active| = r:

**Basic:** tr(G X_t) = 1 for generalized inverse G (1 eq per active term)

**Enhanced additions:**
- LEFT null (n^T M = 0): n^T X_t = 0 → 9 eqs per (null vector, active term)
- RIGHT null (Mn = 0): X_t n = 0 → 9 eqs per (null vector, active term)
- For rank-3: (9-3)×3×9×2 = 324 extra eqs per contraction
- For rank-6: (9-6)×6×9×2 = 324 extra eqs per contraction
- Rank-9: no null space → no extra equations

### Bug fixes in this ARTIFACT:
1. Trace coefficient transposition: tr(GX) = sum G[i,j]X[j,i], so coeff of X_t[b,c] is G[c,b]
2. Null space computation direction: gf2_nullspace(M) gives LEFT null, gf2_nullspace(M.T) gives RIGHT null

### Files created:
- [swap_search_n22.py](../code/swap_search_n22.py) - Hill-climb swap search for n=22
- [pipeline_n22.py](../code/pipeline_n22.py) - Full pipeline: search → trace → Brent
- [enhanced_trace_filter.py](../code/enhanced_trace_filter.py) - Trace + nullspace filter (fixed)
- [verify_cslot_flattening.py](../code/verify_cslot_flattening.py) - Slot flattening verification
- `workspace/data/swap_search/` - All candidate results
- `workspace/data/pipeline_results/` - Pipeline batch results (in progress)

### Open questions:
1. Can ANY n=22 A-multiset pass all filters + Brent? (If not → R ≥ 23)
2. Can the enhanced filter be further strengthened with rank-one minor conditions?
3. Can the E11 route (8-dim quotient, rank 19) escape the difficulty?
4. What is the structure of the Brent UNSAT — which equations are hardest?

### Flattening verification:
- All three slot flattenings (A,B,C) with correct grouping are 27×27 permutation matrices, rank 27
- Σ rank(a_t) ≥ 27, Σ rank(b_t) ≥ 27, Σ rank(c_t) ≥ 27 for any decomposition
- A-slot rank-3 result was due to wrong index grouping; corrected to rank 27
