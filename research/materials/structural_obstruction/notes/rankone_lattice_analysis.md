# Rank-One Lattice Analysis — Corrected and Validated

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Summary

Three exact analyses show no rank-22 decomposition of $T_{\langle3,3,3\rangle}$ over $\mathbb F_2$ lies within any known rank-23 decomposition span. Local retained-neighborhood exclusions are validated but remain local: they do not prove a global lower bound.

## 1. $KC^T = D$ Equivalence

For A-masks $a_t$ and B-masks $b_t$, define $K_{(\alpha,\beta),t} = a_{t,\alpha} b_{t,\beta}$ and $D_{(\alpha,\beta),\gamma} = T_{\alpha\beta\gamma}$. Then $KC^T = D$ is exactly the 729 Brent equations. A rank-$n$ decomposition exists iff $n$ rank-one $9\times 9$ matrices over $\mathbb F_2$ span a subspace containing $W = \mathrm{col}(D)$.

## 2. $W$ Contains Zero Rank-One Matrices

For $3\times 3$ matrix multiplication, each element $M_X \in W$ satisfies $\mathrm{rank}(M_X) = 3\,\mathrm{rank}(X)$ after block-diagonal identification. Since rank 1 is not a multiple of 3 for $X\neq 0$, $W$ contains no nonzero rank-one matrices. This is a property of the tensor structure, not a computational observation.

## 3. Within-Span Rank-One Lattice (Complete Exclusion)

Enumeration algorithm: for each $a \in \mathbb F_2^9 \setminus \{0\}$, the map $b \mapsto a \otimes b$ is linear; computing its kernel in the span gives all rank-one matrices with that A-factor. This is exhaustive over all 511 A-values.

| Source | Rank-ones in 23-dim span | Extra | Best hyperplane rank-one rank | All 16,383 hyperplanes tested |
|--------|--------------------------|-------|-------------------------------|-------------------------------|
| cn122  | 29 | 6 (sums of 2 original) | 21 | Yes |
| flip   | 26 | 3 | 20 | Yes |
| pivot17| 26 | 3 | 20 | Yes |

No rank-22 decomposition has its column span inside any known rank-23 span.

## 4. Fiber Test for $d < k$ Blocks (Fixed and Validated)

review (analysis) identified a bug: the original `fiber_test` dropped `tag=0` entries from nonzero-remainder fibers. Fixed in `fiber_resolution.py` (line 78: `if (rem != 0 or tag != 0) and tag not in fibers2[rem]`).

### Brute-force validation
On block $(0,12,14,21)$ with $d=2, k=3$:
- 251,019 distinct quotient vectors
- 138,955 nonzero fibers have tag=0 entries (now properly included)
- Brute-force best combined E-rank: 1 (target $d=2$)
- **Fixed fiber test agrees with brute force**: True

### Fixed results

| $k$ | Unique $d<k$ sets | Status | All slack-one? |
|-----|-------------------|--------|----------------|
| 3   | 5                 | All NO_FIBER_COVER | Yes ($d=2, k=3$) |
| 4   | 144 (pending re-run) | Expected NO_FIBER_COVER | Yes ($d=3, k=4$) |

### Positive controls (unchanged by fix)
- d=k k=1: 23/23 pass
- d=k k=2: 250/250 pass
- Synthetic extra-rank-one: 6/6 pass
- Brute-force cross-check: 1/1 match

## 5. Corrected k=5 Scan Results

| Category | Count |
|----------|-------|
| $d \geq 6$ (impossible) | 409,092 |
| $d = 5 = k$ (tag-rank $< 5$, excluded) | 185,088 |
| $d = 4 < k$ (slack 1, needs fiber test) | 11,454 |
| $d = 3 < k$ (slack 2, needs extended test) | 48 |

The 48 slack-2 blocks ($d=3, k=5, k-d=2$) need a 2-dimensional outside subspace search, not the single-direction fiber test.

## 6. Scope

These results exclude rank-22 decompositions:
- within known rank-23 spans (complete)
- near known rank-23 schemes (k=3,4 neighborhoods of cn122; k=5 partially)

They do NOT prove $R_{\mathbb F_2}(T) \geq 23$ or $\geq 21$.

## Key Files
- [rankone_lattice.py](../code/rankone_lattice.py): within-span analysis
- [fiber_resolution.py](../../quotient_cores/code/fiber_resolution.py): FIXED fiber test
- `workspace/data/rankone_lattice/`: lattice outputs
- `workspace/data/fiber_fixed/`: fixed fiber outputs
