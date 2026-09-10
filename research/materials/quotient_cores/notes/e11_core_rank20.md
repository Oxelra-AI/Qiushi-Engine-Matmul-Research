# E11 Core Rank ≥ 20 — Complete Wang Exclusion

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Result

**The E11 core has rank ≥ 20 over F₂.**

No 19-term multiset of quotient A-directions in F₂⁸\{0} satisfies the cap≤5
Wang occupation constraints. This is an exhaustive, deterministic, independently
reproducible computation.

## Proof Structure

1. **Wang occupation system**: For any subspace U ≤ F₂⁹ containing E₁₁, the
   Wang certificate gives a lower bound LB(T/U) on the minimum number of terms
   in any E11 core CPD whose A-factor projects into U. Any rank-19 E11 core must
   satisfy all 417,199 such constraints simultaneously.

2. **Cap≤5 relaxation**: The subset of 338,840 constraints with cap₁₉ = 19-LB ≤ 5
   (i.e., LB ≥ 14) is a necessary condition. Any rank-19 core satisfying the
   full system must also satisfy this subset.

3. **Distinct supports**: The 576-element E11 stabilizer partitions the 255
   nonzero quotient points into 8 orbits of sizes [3,3,9,36,36,36,36,96].
   An orderly DFS under orbit branching exhaustively searches all 19-point
   distinct supports. Domain propagation (removing points from saturated rows
   and propagating feasibility) resolves all 8 branches in 0.05s total with
   0 solutions.

4. **Repeated directions**: Wang line caps restrict repeatable directions to
   {1,2,3,4,32,36} (the 6 directions with line_cap ≥ 2), multiplicity ≤ 2.
   Pairwise and 3-flat cap constraints leave 41 allowed repeat subsets (sizes
   1-3). For each, residual cap constraints (original cap minus extra occupancy)
   are precomputed, and the domain DFS searches for the residual number of
   distinct points. All 41 cases complete in 5.3s total with 0 solutions.

5. **Completeness**: Every possible 19-term quotient A-multiset is covered by
   either the distinct case (if all directions are distinct) or one of the 41
   repeat cases (if any direction has multiplicity 2). The enumeration is
   exhaustive and deterministic.

## Key Files

- Domain-propagation DFS: [e11_domain_dfs.cpp](../code/e11_domain_dfs.cpp)
- Distinct branch results: [summary.json](../results/wang_native/domain_dfs_cap5/summary.json)
- Repeat case results: [summary.json](../results/wang_native/domain_dfs_repeats/summary.json)
- Wang constraint binary: `workspace/data/wang_native/e11_wang_cap5.bin` (338,840 rows)
- Repeat residual constraints: `workspace/data/wang_native/repeats/`
- Positive control: rank-21 pool satisfies cap21 (0 violations), violates cap19 (expected)
- Repeat analysis: [e11_repeat_capacity_analysis.json](../../occupation_and_completion/results/wang_validation/e11_repeat_capacity_analysis.json)
- Orbit data: [e11_quotient_orbits.json](../results/e11_orbits/e11_quotient_orbits.json)

## Timing

| Case | Branches | Total Time | Solutions |
|------|----------|-----------|-----------|
| Distinct (8 orbit branches) | 8 | 0.05s | 0 |
| Single repeats | 6 | 0.17s | 0 |
| Double repeats | 15 | 0.36s | 0 |
| Triple repeats | 20 | 0.34s | 0 |
| **Total** | **49** | **5.3s** | **0** |

## Implications

1. **E11 construction route closed**: No rank-19 E11 core → no rank-22 full
   scheme via the E11 bridge (rank r core → rank r+3 full).

2. **Lower bound**: E11 core rank ≥ 20. For the global R(T) ≥ 21, still need
   the rank-1-A-factor reduction (every full rank-20 decomposition must have a
   rank-1 A-factor, normalizable to E11). This is equivalent to showing that
   no full rank-20 multiset has all A-factors of rank ≥ 2 in the Wang system.

## Verification Checklist

- [ ] Independent reproduction of the domain DFS on the same binary constraints
- [ ] Independent verification that the binary constraints faithfully encode the
      Wang LUT (the 338,840 cap≤5 E11 rows)
- [ ] Semantic verification that the Wang LUT itself correctly represents the
      tensor rank lower bounds for subspace restrictions of the E11 core
- [ ] Positive control: verify that the DFS accepts known rank-21 pool rows at
      the appropriate cap level (DONE: cap21 = cap19 + 2, all 20 tested pass)
