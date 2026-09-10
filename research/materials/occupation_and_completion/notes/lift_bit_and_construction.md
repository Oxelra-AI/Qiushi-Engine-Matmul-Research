# Research Note: Lift-Bit Layer and Construction Bottleneck

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Key Results

### 1. Independent Lift-Bit Verification (CRITICAL)
The rank-2 Wang-admissible support `[1,3,9,33,99,128,132,144,148,160,184,189,192,198,209,215,224,249,254]`
is **lift-infeasible** against the full Wang LUT at cap≤5:
- Script: [lift_bit_direct.py](../code/lift_bit_direct.py)
- Result: [rank2_sup1_lut_cap5.json](../results/lift_bit/rank2_sup1_lut_cap5.json)
- DFS: 177 nodes, 5,172,126 binding rows, 306.9s
- Cap distribution: {1:38, 2:103803, 3:1269503, 4:1791010, 5:2007772}
- Dim distribution: {1:38, 2:8987, 3:329066, 4:2257533, 5:2455554, 6:120948}

**dim≤3 alone is INSUFFICIENT**: using only the dim≤3 binary (831k rows), the support
is FEASIBLE (41 nodes). Infeasibility requires dim≥4 full-tensor rows.

This is an independent check of the lift infeasibility stated above.

### 2. Forced-Tightness Incidence Bounds
Script: [quotient_saturation_incidence.py](../../deformation_and_incidence/code/quotient_saturation_incidence.py)
Results: `workspace/data/saturation/{e11,rank2,rank3}_n19_saturation.json`

For all three quotients at n=19, the LP-based forced-tightness lower bound is **zero**
(negative for every rank class). The uniform incidence counting route cannot produce
an unconditional lower bound on tight contractions. Per-support filtering remains the
only viable trace-based approach.

### 3. Enhanced Trace Filter: Nullspace Vacuity for Rank-2
Tested the nullspace strengthening (v_t ∈ col(M_λ), w_t ∈ row(M_λ))
on both known rank-2 admissible supports. Both have **only rank-9 tight contractions**,
where nullspace is empty (full-rank matrices). Enhanced filter gives identical
rank/aug [714,715] as the trace-only filter.

For E11, tight contractions include rank-3 and rank-6 (verified on the rank-21 control:
3 rank-3, 3 rank-6, 2 rank-9 tight rows), where nullspace conditions give
2(9-r)*9 equations per active term — genuinely powerful. The enhanced filter matters
only for E11 construction, not for rank-2/rank-3 lower-bound supports.

### 4. Construction Pipeline Failures
- **E11 CEGAR** (CP-SAT with integer multiplicity): completely stuck, no output in 1800s
- **E11 hill-climb** (Python, 417k rows): too slow, no output in 1800s  
- **Rank-2 census** (CP-SAT with blocking): no output in 3600s
- **C++ hill-climb**: compiled but memory issue with full per-point index

The E11 construction bottleneck is the violation-checking cost per swap (417k rows).
The existing compiled `workspace/scripts/wang_hillclimb` binary (from analysis) found
8-violation E11 n=19 supports and should be the starting point for faster search.

### 5. Related Lift-Cut Results
- research_record independently found 2 rank-2 admissible supports, both lift-infeasible
- Produced 96 stabilizer-orbit cuts from 2 minimized 12-point lift cuts
- **Correction**: 96 cuts are tautological in rank-2 branches 1-5 (all contain orbit O={1,3,9} points)
- Rank-3 branch 1 closed by DFS (584s, 0 supports)
- analysis Python CEGAR had binary parser bug; C++ DFS closures remain valid

## Architecture Summary

Three constraint layers for rank-20 exclusion at quotient n=19:
1. **Quotient Wang occupation** (417k rows, 255 binary vars): necessary, insufficient for rank-2
2. **Full-tensor lift-bit constraints** (5M+ binding rows): sees structure lost in quotient projection; 
   rejects Wang-admissible supports; requires dim≥4 rows
3. **Brent completion** (6k+ variable CNF): definitive but expensive (944s per support)

The viable lower-bound proof route is Layer 1+2 closure: enumerate Wang-admissible supports
via CEGAR, reject each via lift-bit DFS, until CEGAR reports INFEASIBLE (no supports remain).
The viable upper-bound route is E11 construction: find a Wang-admissible n=19 support
that passes trace filter AND Brent completion.
