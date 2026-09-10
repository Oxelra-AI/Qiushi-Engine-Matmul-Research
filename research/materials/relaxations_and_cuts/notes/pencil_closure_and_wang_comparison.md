# Pencil Route Closure and Wang Comparison

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Algebraic Theorem

**Nilpotent-Idempotent Rank Bound.**  For N,W ∈ F₂^{n×n} with N²=0 and W²=W:

  rank(N + W) ≥ rank(N).

*Proof:* W maps ker(N+W) into ker(N) ∩ im(W) with kernel in ker(W) ∩ ker(N).
Since ker(W) ∩ im(W) = {0} (idempotent), both pieces are disjoint in ker(N).
Hence dim ker(N+W) ≤ dim ker(N).  ∎

## Application to (3,9,9) Lines

For any (3,9,9) E11 core dual line D = span(q₁,q₂):
- M₁ = L(q₁) = Q₁ ⊗ I₃ rank 3, M₂ = L(q₂) = Q₂ ⊗ I₃ rank 9
- N = M₂⁻¹M₁ = H₀ ⊗ I₃, H₀ = Q₂⁻¹Q₁ rank 1
- I₃+H₀ = Q₂⁻¹(Q₁+Q₂) has rank = rank(Q₁+Q₂) = 3 (since third contraction is rank 9)
- rank(I₃+H₀) = 3 forces H₀² = 0: if H₀ were idempotent, rank(I+H₀) = 2 ≠ 3
- Therefore N² = 0 ✓, verified computationally on all 468 lines

The theorem then gives: any color budget (c₁₀,c₀₁,c₁₁) with
c₁₁ + c₀₁ ≤ 9 (forcing W idempotent) must have c₁₀ ≥ 3.

## Wang Comparison: Pencil Is Redundant

**All 468 (3,9,9) lines have L(D⊥_lifted) = 12.**

Wang bound for D⊥ (6D core, 7D lifted): c₀₀ ≤ 19 - 12 = 7.
When w(q₂) = 9 (the tight case where W is forced idempotent):
  occupation = c₁₀ + 9, so c₀₀ = 10 - c₁₀.
  Wang: 10 - c₁₀ ≤ 7, so c₁₀ ≥ 3.

**Wang already implies c₁₀ ≥ 3, identical to the pencil theorem.**

## N² Classification for All Types with Rank-9 Contraction

| Type     | N²=0  | N²=N   | Other | Pencil applicable |
|----------|-------|--------|-------|-------------------|
| (3,6,9)  |   0   | 2880   |   0   | NEVER             |
| (3,9,9)  | 936   |   0    | 936   | All (via rank-3)  |
| (6,6,9)  |   0   |   0    | 6336  | NEVER             |
| (6,9,9)  |   0   |   0    | 6048  | NEVER             |
| (9,9,9)  |   0   |   0    | 1152  | NEVER             |

Types (3,3,3), (3,3,6), (3,6,6), (6,6,6) lack invertible contractions.

## Wang Sufficiency Across All Types

| Rank Type  | Count | min L | Wang c₁₀≥ | Pencil c₁₀≥ | Redundant |
|------------|-------|-------|-----------|-------------|-----------|
| (3,3,3)    |   50  |   6   |     3     |     3       |   YES     |
| (3,3,6)    |  378  |   6   |     0     |    n/a*     |   n/a     |
| (3,6,6)    | 1377  |   9   |     3     |     3       |   YES     |
| (3,6,9)    | 1440  |   9   |     0     |    n/a*     |   n/a     |
| (3,9,9)    |  468  |  12   |     3     |     3       |   YES     |
| (6,6,6)    | 2210  | 9-12  |     3     |    n/a*     |   n/a     |
| (6,6,9)    | 3168  |  12   |     3     |    n/a*     |   n/a     |
| (6,9,9)    | 1512  |  12   |     3     |    n/a*     |   n/a     |
| (9,9,9)    |  192  |  14   |     5     |    n/a*     |   n/a     |

*n/a: pencil theorem (N²=0) does not apply for these types.

## Near-Miss Violation Structure

Support [1,2,3,4,8,20,24,31,32,36,64,73,109,127,128,141,160,182,219]:
- 8 Wang violations, all L=12, excess 1
- 6 at dimension 5, 2 at dimension 6
- Both dim-6 violations are D⊥ for (3,9,9) lines:
  D=[87,9] with ranks (9,3,9) and D=[133,18] with ranks (9,3,9)

## Conclusion

The dual-line pencil route is closed for the E11 distinct-core problem:

1. The only type where the nilpotent theorem applies is (3,9,9).
2. For (3,9,9), L(D⊥) = 12 uniformly, making Wang already sufficient.
3. For all other types, N has wrong algebraic structure for the theorem.
4. No pencil type adds support-level restrictions beyond the complete Wang table.

## Wang L-Distribution by Core Dimension

| Core dim | Full dim | Total    | L≥12     | Key L values              |
|----------|----------|----------|----------|---------------------------|
| 7        | 8        | 511      | 0        | L=3:49, L=6:294, L=9:168  |
| 6        | 7        | 43,435   | 26,628   | L=9:15827, L=12:25284, L=14:1344 |
| 5        | 6        | 788,035  | 773,090  | L=12:291K, L=14:297K, L=15:123K |
| 4        | 5        | 3,309,747| 3,309,698| All L≥12                  |
| 3        | 4        | 3,309,747| 3,309,747| All L≥12                  |
| 2        | 3        | 788,035  | 788,035  | All L≥15+                 |
| 1        | 2        | 43,435   | 43,435   | All L≥17                  |
| 0        | 1        | 511      | 511      | All L=19                  |

**99.6% of all 8.28M Wang rows have L ≥ 12.**

The near-miss violations are at core dim 5 (6 violations) and core dim 6
(2 violations), all L=12. These sit at the WEAKEST layer of the strong
constraint system: the boundary between L=12 and L=9/11 at dim 5-6.

**Next direction:** Global occupation incidence — systematic proof methods
combining multiple Wang rows (PB/Farkas cuts, dimension-5/6 interactions)
or finding a complete-Wang-admissible support for exact B/C completion.
The dim-5 L=12 layer (291K subspaces) and dim-6 L=12 layer (25K subspaces)
are the primary targets for global obstruction analysis.
