# Complete synthesis — KY tangent isolation and m≥5 calibration

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Major results this ARTIFACT

### 1. BILR first-order isolated in KY stratum (NEW, verified at two primes)

The 1134×1134 KY matrix of the BILR residual cubic has rank 722, corank 412.
Of the 32 internal frame tangent directions (4 planes × 8 sl₃ basis):
- 8 torus directions (H₁, H₂ per plane) fix R exactly (δR = 0): trivially tangent
- 24 non-torus directions all have positive rank(V^T KY(δR) U):
  - E₁₂: 84/70, E₁₃: 50/18, E₂₁: 26/16, E₂₃: 32/11, E₃₁: 26/16, E₃₂: 76/69
    (first number mod 65521, second mod 32003)
- Ranks are perfectly orbit-independent (Z₄ equivariance)

**Meaning after analysis scope repair:** KY rank is lower semicontinuous. Since BILR has KY rank 722, a sufficiently small neighborhood of the displayed frame already avoids KY ≤ 700. The analysis tangent computation adds the sharper local structure: inside the internal-frame parameter space, the Zariski tangent to {KY ≤ 722} at BILR consists only of the 8 gauge directions that fix R exactly. Thus the low-KY locus through BILR is locally no larger to first order than the gauge orbit; this is a local statement near BILR, not a finite-distance exclusion.

### 2. Klein V₄ conjugacy-consistent with BILR (NEW)

After correcting an eigenbasis conversion bug, all 8 Klein V₄ and all 8 C₄ regular
F₅ points match BILR's PGL₃-invariant signature:
- det restricted to each plane ≡ 0
- Killing conic det = −2 (= 3 mod 5) on all 4 planes

Both chart dimensions (2) = dim C_{PGL₃}(H), consistent with slicing one orbit.
No inequivalent exterior component has been found by any symmetric ansatz.

### 3. m≥5 KY calibration (NEW)

For rank-22 cyclic (f, m) with f+3m=22:
| f   | m | KY threshold 70f | BILR partial cube KY |
|-----|---|-------------------|----------------------|
| 10  | 4 | 700               | 722 (11 cubes)       |
| 7   | 5 | 490               | 490 (first 7 cubes)  |
| 4   | 6 | 280               | 280 (first 4 cubes)  |
| 1   | 7 | 70                | 70 (first 1 cube)    |

BILR's cubes EXACTLY saturate 70k for k=1,4,7 (zero cancellation among
independent cube subsets). This shows the KY threshold is tight: the right
cubes can hit it exactly. The m≥5 question is whether there exist exterior
configurations (5,6,7 free orbits) whose residuals are exactly f cubes.

## Scientific state after analysis

### (10,4) branch: heavily constrained but not closed
- The exterior fiber is likely one PGL₃ orbit (BILR-type, from symmetric ansätze)
- Within that orbit, the {KY ≤ 722} tangent at BILR is only the 8-dimensional gauge tangent; nearby KY ≤ 700 is absent by semicontinuity
- The BILR residual has exact Waring rank 11 (three independent certificates)
- Closing (10,4) requires either:
  a. Proving BILR is the ONLY rank-4 exterior component (not just symmetric ones)
  b. Showing the rank-10 locus is empty in the whole frame family (not just first order)
  c. A direct constructive search for rank-10 residuals at special strata

### m≥5 branches: genuinely open, with tight KY thresholds
- BILR has f=11, m=4 (rank 23), proving trace-grading fails at m≥5
- The skeletons (7,5), (4,6), (1,7) are the three open m≥5 branches
- Entry condition: residual KY ≤ 70f (tight, as BILR calibration shows)
- The peel-one-plane approach (ω − p ∈ σ_{m-1}(G(3,8))) and
  Strassen/commuting Hessian reconstruction are the natural instruments

### Non-cyclic: independent-UV rank-one-span remains the only global formulation

## Key files
- [ky_tangent_at_bilr.json](../../deformation_and_incidence/results/ky_tangent/ky_tangent_at_bilr.json): tangent computation
- [klein_conjugacy_discriminants.json](../../symmetry_and_residuals/results/klein_conjugacy/klein_conjugacy_discriminants.json): conjugacy
- [ky_tangent_at_bilr.py](../../deformation_and_incidence/code/ky_tangent_at_bilr.py), `klein_conjugacy_check.py`
- [ky_tangent_and_klein_conjugacy.md](../../deformation_and_incidence/notes/ky_tangent_and_klein_conjugacy.md): detailed write-up
