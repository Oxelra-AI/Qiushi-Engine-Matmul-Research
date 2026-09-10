# Coding-Theory Framework and Support Enumeration

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Generalized Hamming Weight vs Singleton Bound

### Framework

For a rank-19 E11 core decomposition, the 19 distinct quotient A-directions
q_1,...,q_19 ∈ F₂^8 form the columns of an 8×19 matrix M. The rowspace
C = rowspace(M) is a [19,8] binary code (k=8 is forced because every
hyperplane has Wang LB ≥ 3, so all 19 points can't fit in any hyperplane).

For a subspace Ψ ≤ F₂^8 of dimension d, the annihilator A = Ψ^⊥ has
dimension r = 8-d. The subcode D_A ≤ C has support {t : q_t ∉ Ψ}, and
the Wang constraint gives |supp(D_A)| ≥ LB(span(E₁₁, lift(Ψ))).

So the r-th generalized Hamming weight satisfies:
  d_r(C) ≥ L_r := min_{dim(V)=9-r, E₁₁∈V} LB(V)

The generalized Singleton bound: d_r(C) ≤ n - k + r = 11 + r.

### Results

Computed L_r by iterating all 8.2M Wang LUT entries with O(1) E₁₁-membership
check on packed RREF keys:

| r | dim9 | #subsp | L_r | Singleton | gap | Result |
|---|------|--------|-----|-----------|-----|--------|
| 0 | 9    | 1      | 0   | 11        | 11  | slack  |
| 1 | 8    | 255    | 3   | 12        | 9   | slack  |
| 2 | 7    | 10795  | 6   | 13        | 7   | slack  |
| 3 | 6    | 97155  | 9   | 14        | 5   | slack  |
| 4 | 5    | 200787 | 11  | 15        | 4   | slack  |
| 5 | 4    | 97155  | 14  | 16        | 2   | slack  |
| 6 | 3    | 10795  | 15  | 17        | 2   | slack  |
| 7 | 2    | 255    | 17  | 18        | 1   | slack  |
| 8 | 1    | 1      | 19  | 19        | 0   | TIGHT  |

**No Singleton violation.** The gaps narrow from 11 down to 0.

E₁₁-containing min LBs exactly match all-subspace min LBs at every dimension.
Data: [ghw_singleton_test.json](../results/ghw_singleton/ghw_singleton_test.json).

## Orderly DFS Support Enumeration

### Cap≤3 DFS (118K Wang rows)
- 31,776+ complete 19-point supports from branch 1 alone (column 1 start)
- Tree narrows from 1 node at depths 1-11 to 53,934 at depth 19
- Time: 90s for one branch

### Cap≤5 DFS (339K Wang rows)
- First branch reached depth 16 with only 30 nodes in 90s
- Tree profile: depths 1-7 single path, broadens at 8-13 (~10K), narrows sharply

### Full Wang Check of Cap≤3 Solutions
**Critical finding**: 0/31,776 cap≤3 solutions survive cap 4-8 constraints.
- 100% rejection rate
- ALL failures at cap=7 (LB=12) constraints
- These are dim-6 hyperplane-type constraints that force spreading

Data: [cap3_stream_cap48_check.json](../results/ghw_singleton/cap3_stream_cap48_check.json).

## Pool Coordinate Convention

**Critical correction discovered**: the rank-21 pool (mod2-rank21a.npy) stores
core A-masks using bits 0-7 for core slices 0-7, NOT the full-tensor convention
where bits 1-8 are core slices. Verified:
- Brent reconstruction with bits 0-7: diff = 0 ✓
- Brent reconstruction with bits 1-8: diff = 45 ✗

For Wang constraint checking on pool data, the correct quotient direction is
q = pool_u & 255 (identity map), NOT core.project9(pool_u).

This does NOT affect the DFS or GHW results (which work in the 8-bit quotient
space directly), but DOES affect any pool-based Wang validation.

## Open Background Task
- `s7_t22_tool1`: Cap≤5 DFS with all 8 orbit representatives, 600s time limit
  Purpose: determine if ANY 19-point support survives all cap≤5 Wang constraints
  If 0 solutions → strong evidence for E11 core rank ≥ 20

## Implications
The 100% rejection of cap≤3 solutions by cap=7 constraints means the Wang
occupancy system at the LB=12 level is extremely restrictive. If the cap≤5
DFS also returns 0, the complete Wang table excludes all 19-point supports,
proving the E11 core has rank ≥ 20 (within the Wang certificate's validity).
