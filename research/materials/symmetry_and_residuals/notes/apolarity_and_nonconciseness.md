# Cyclic apolarity and non-conciseness analysis

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Summary of new results

### BILR S_{2fix-Z₃} (2,7) verification and calibration

Reconstructed the BILR Section 2.4 rank-23 decomposition with (f,m)=(2,7): 2 cubes + 7 free Z₃ orbits = 23 terms. Verified 0 Brent errors. The residual cubic (tr(M³) minus orbit products) equals the sum of the 2 displayed cubes exactly (integer third-derivative tensor match).

Key invariants of the (2,7) residual cubic:
- Catalecticant shape: 9 × 45, rank 2 modulo primes 1000003, 65521, 32003
- Annihilator dimension: 7 (= 9 - 2)
- Koszul-Young flattening rank: 140 modulo primes 1000003, 65521
- This equals exactly 2 × 70, confirming 70 per independent cube (the Koszul-per-cube upper bound is tight at this calibration point)

Data: [bilr_27_basic.json](../results/bilr_27/bilr_27_basic.json), [annihilator_perturbation.json](../results/bilr_27/annihilator_perturbation.json), `data/bilr_27/full_first_order_analysis.json`.

### First-order annihilator perturbation: (1,7) locally blocked

For a (1,7) cyclic rank-22 scheme to exist, the residual cubic must be a single cube (catalecticant rank 1, annihilator dimension 8). Starting from the BILR (2,7) point (catalecticant rank 2), I analyzed all 56 internal SL₃ perturbation directions (7 orbits × 8 sl₃ generators).

**Two-stage analysis:**

1. **Annihilator-preserving condition** (does the perturbation keep catalecticant rank ≤ 2?):
   - Constraint matrix: 315 × 56, rank 42
   - Annihilator-preserving kernel: 14 dimensions
   - The 42 non-preserving directions all INCREASE the catalecticant rank

2. **Row-space collapse condition** (among annihilator-preserving directions, does the rank drop from 2 to 1?):
   - All 14 annihilator-preserving directions leave the catalecticant COMPLETELY unchanged (verified: singular values identical at all tested perturbation magnitudes ε = 0.001, 0.01, 0.1, 1.0)
   - These 14 directions are the isotropy of the residual under internal SL₃: they change the orbit basis vectors but leave the total orbit product (and hence the residual cubic) invariant
   - 2 of the 14 directions were identified as global sl₃ stabilizer generators

**Conclusion:** At the BILR (2,7) point, no first-order internal SL₃ deformation can decrease the catalecticant rank. The (1,7) skeleton is first-order blocked at this calibration point. This is a LOCAL result at the BILR (2,7) point within the fixed rank-7 exterior decomposition; it does not cover other rank-7 exterior decompositions.

### Koszul-per-cube calibration table

| Point | Cubes (f) | Koszul rank | Upper bound (70f) | Tight? |
|-------|-----------|-------------|-------------------|--------|
| BILR (2,7) | 2 | 140 | 140 | Yes |
| BILR (11,4) | 11 | 722 | 770 | Within 7% |

For the m=4 rank-22 question: (10,4) needs f=10 cubes. The Koszul upper bound is 700. The BILR (11,4) residual has Koszul rank 722 > 700. By semicontinuity, the Koszul rank is ≥ 722 on the irreducible component of the rank-4 exterior fiber containing the BILR point. On that component, no residual can have Waring rank ≤ 10, hence no (10,4) cyclic rank-22 decomposition.

**The remaining gap for m=4:** Are there OTHER irreducible components of the rank-4 exterior fiber of ω? If the fiber is irreducible (a single PGL₃ orbit), the semicontinuity argument closes m=4 completely.

### m ≥ 5 non-conciseness structure

For cyclic rank-22 with m ≥ 5 free orbits: f = 22 - 3m ≤ 7 < 9. The residual cubic C = tr(M³) - 3∑ orbits has Waring rank f, hence catalecticant rank ≤ f ≤ 7 < 9 (non-concise). The annihilator Ann(C) has dimension ≥ 9 - f ≥ 2.

For each annihilator direction a ∈ Ann(C):
$$\partial_a \mathrm{tr}(M^3) = 3 \sum_s [\ell_{U_s}(a)\ell_{V_s}\ell_{W_s} + \ell_{U_s}\ell_{V_s}(a)\ell_{W_s} + \ell_{U_s}\ell_{V_s}\ell_{W_s}(a)]$$

i.e., tr(aM²) must be expressible as a sum of specific quadratic forms built from the orbit vectors. This gives 45 independent quadratic conditions per annihilator direction.

Skeleton-by-skeleton:
- **(10,4)**: f=10, concise (cat rank 9), needs Koszul analysis (above)
- **(7,5)**: f=7, ann dim ≥ 2, 2×45 = 90 extra quadratic conditions
- **(4,6)**: f=4, ann dim ≥ 5, 5×45 = 225 extra quadratic conditions
- **(1,7)**: f=1, ann dim = 8, 8×45 = 360 extra quadratic conditions

The (1,7) case is the most constrained: the residual must be a perfect cube. The review observes this is "one cube less than a published algorithm" — the BILR (2,7) achieves ann dim 7, and (1,7) requires ann dim 8.

### Fiber irreducibility: the remaining proof gap

The decisive open question for both m=4 and m≥5 is whether the relevant exterior fibers (rank-4, rank-5, rank-6, rank-7) have other irreducible components beyond those containing the known calibration points.

For the rank-4 fiber (m=4):
- Expected dimension: 4×16 - 56 = 8 = dim Stab(ω) = dim PGL₃
- BILR exterior Jacobian: rank 56 with 40-dim kernel (32 internal SL₃ + 8 global adjoint)
- This confirms the fiber is smooth and 8-dimensional at the BILR point
- The Stab(ω) orbit has dimension 8, so locally the fiber is a single orbit
- Global irreducibility requires either algebraic proof or enumerative computation

A numerical orbit equivalence check between the BILR and analysis numerical decomposition was attempted but blocked by sl₃ coordinate convention issues (inner-product vs actual coordinates) and optimizer timeout. The convention mismatch was identified: the Gram matrix for the sl₃ basis is not the identity (diagonal [1,1,1,1,1,1,2,2], det = 3). This affects all sl₃ coordinate computations and must be corrected when converting between gl₃ and sl₃ representations.

### Relation to the general problem

The cyclic family results (m≤3 excluded in characteristic zero, m=4 Koszul-excluded on the BILR component, m≥5 non-conciseness constrained) constitute the strongest structured family analysis achieved. However:

1. The cyclic family does NOT cover mixed inner-by-outer symmetries (e.g., BILR's own Z₄×Z₃)
2. The cyclic family does NOT cover the general nonsymmetric independent-UV incidence
3. The BILR Z₄×Z₃ scheme is not purely cyclic (it has additional inner Z₄ symmetry)

The next natural targets are:
- Prove rank-4 exterior fiber irreducibility (closing m=4 completely)
- Develop the non-conciseness elimination for m≥5 (starting from (1,7))
- Analyze mixed inner-by-outer families (BILR Z₄×Z₃ as calibration)
- Return to the general independent-UV incidence
