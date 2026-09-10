# SA/RLT pair-correlation lift — theoretical analysis

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Mathematical setup

For the E11 quotient (F_2^8, 255 nonzero directions), the distinct-19 support problem is:

Find x_p ∈ {0,1} for p=1,...,255 with Σ x_p = 19, satisfying all 417,199 Wang occupation inequalities Σ_{q∈U\{0}} x_q ≤ 19-L(U) for each subspace U.

### Sherali-Adams first lift

Introduce pair variables y_{pq} relaxing x_p · x_q for unordered {p,q}. Standard SA/RLT constraints:
- y_{pp} = x_p (self-pair)
- 0 ≤ y_{pq} ≤ min(x_p, x_q) (McCormick upper)
- y_{pq} ≥ x_p + x_q - 1 (McCormick lower)
- Σ_{q≠p} y_{pq} = 18·x_p (pair cardinality from total=19)

Wang RLT: multiply each row by x_p or (1-x_p):
- x_p side: Σ_{q∈U} y_{pq} ≤ cap(U)·x_p
- (1-x_p) side: Σ_{q∈U} (x_q − y_{pq}) ≤ cap(U)(1−x_p)

### Key cap-1 mechanism

For a cap-1 subspace U (cap = 19-L = 1) with nonzero points {p, q, p⊕q}:
- If point p is selected (x_p > 0): the x_p-side RLT gives
  y_{pp} + y_{pq} + y_{p,p⊕q} ≤ 1·x_p = x_p
  Since y_{pp} = x_p: y_{pq} + y_{p,p⊕q} ≤ 0
  Both being ≥ 0: y_{pq} = y_{p,p⊕q} = 0.

So cap-1 dim-2 subspaces force pair variables to zero for all cross-pairs within them.

### Cap distribution (from analysis)
- dim 1: cap=1 (249), cap=2 (6) → 255
- dim 2: cap=1 (438), cap=2 (9830), cap=3 (525), cap=4 (2) → 10,795
- dim 3: cap=2 (24828), cap=3 (58428), cap=4 (12801), cap=5 (1098) → 97,155

### Orbit structure
Point orbits under E11 stabilizer (|G|=1152): 6 orbits of sizes [96, 72, 36, 36, 9, 6].
- The 6-element orbit contains the 6 capacity-2 dim-1 directions (rulings through E11).
- The other orbits partition the 249 capacity-1 directions.

### When can the SA lift be infeasible?

The pair cardinality forces each selected direction to have pair-weight 18·x_p distributed among available partners. Cap-1 subspaces reduce available partners. The question is whether the reduced partner graph still admits a valid pair-weighting.

For this to fail, the "forbidden partner" structure from cap-1 subspaces must be dense enough that the cardinality constraint cannot be satisfied. With only ~438 cap-1 dim-2 subspaces out of 10,795 total dim-2, the forbidden fraction is about 4%. This alone seems unlikely to make the LP infeasible.

However, the cap-2 constraints also contribute: for each dim-2 cap-2 subspace, the three cross-pairs must collectively sum to at most 2x_p (if p is in the subspace). With 9,830 such subspaces, these are pervasive budget constraints on pair distributions.

### Next steps based on LP result

**If infeasible**: Major result. Proves R_{F_2}(E11 core) ≥ 20. Need to:
1. Verify with an LP dual certificate or alternative solver
2. Combine with analysis bridge for R_{F_2}(T_{333}) ≥ 21
3. Does NOT imply characteristic-zero rank ≥ 21

**If feasible**: The SA lift alone is insufficient. Next options:
1. Analyze the feasible point structure (which pair orbits are nonzero/zero)
2. Add triangle inequalities: y_{pq} + y_{pr} ≤ x_p + y_{qr}
3. Problem-specific cuts from the Brent structure
4. Use the pair structure to warm-start integer search
5. Consider SA level-2 lift (triple variables)
