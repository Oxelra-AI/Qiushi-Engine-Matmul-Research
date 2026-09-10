# Proof Architecture for R_F2(T_{<3,3,3>}) ≥ 21

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Theorem Statement

Over F_2, the tensor rank of the 3×3 matrix multiplication tensor satisfies
R_{F_2}(T_{<3,3,3>}) ≥ 21.

## Proof Chain

### Layer 0: Wang lower bound (verified)
- Wang's certificate proves R_{F_2}(T) ≥ 20
- Certificate SHA256: `25595a883ce877eecd802139ff4e07646e154b2797ad6fe7f9ec737ab0c6135d`
- Independent replay: [verify_receipt.json](../results/wang_f2_lb20/verify_receipt.json)

### Layer 1: Wang occupation system (verified)
- Complete LUT: 8,283,458 subspace rows, dimension-count matches Gaussian-binomial
- LUT SHA256: from `workspace/data/wang_f2_lb20/wang_subspace_lut.pkl`
- Verification: cn122 rank-23 scheme passes all occupation inequalities

### Layer 2: Multiplicity-free premise (verified)
- All 511 one-dimensional Wang rows have lower bound ≥ 19
- Therefore: in a hypothetical length-20 support, each projective A-direction has
  capacity ≤ 1, so the support is multiplicity-free (Boolean subset of projective space)
- Verification: [k7_unified_manifest.json](../results/k7_manifest/k7_unified_manifest.json) confirms min_lb=19

### Layer 3: Rank-1 factor existence (DRAT verified)
- Branch A: all-rank-3 A-factors → UNSAT (DRAT verified)
- Branch B: rank-2/3 only, no rank-1 → UNSAT (DRAT verified)
- Conclusion: any length-20 decomposition has at least one rank-1 A-factor
- Sources: `workspace/data/wang_capacity_cnf/`, `wang_capacity_cnf_rank2/`

### Layer 4: Normalization to E11
- By GL(3,F2)×GL(3,F2)⋊C2 action, WLOG the rank-1 factor is E11
- The rank-1 factors form a subset of the 49 projective rank-1 points (7×7 Segre grid)

### Layer 5: Global rank-1 cover (verified)
Two exhaustive cases:
- (a) The rank-1 subset contains an adjacent Segre pair → normalizable to {E11, E12} = rep2
- (b) The rank-1 subset has no adjacent pair → it's a matching, with k ≤ 7
- Verification: [rank1_geometry_cover.json](../../occupation_and_completion/results/global_cover/rank1_geometry_cover.json)
- Connection audit: [cover_connection_audit.json](../../occupation_and_completion/results/matching_strata/cover_connection_audit.json)

### Layer 6: Matching branch — orbit enumeration (verified)
- Anchored matchings (fixing E11): 13,327 total, reduced to 38 whole-stabilizer strata
- Strata by k: k=1:1, k=2:1, k=3:3, k=4:7, k=5:10, k=6:10, k=7:6
- Orbit member sum reproduces all 13,327 matchings with 0 mismatch
- Source: [anchored_matching_strata.json](../../occupation_and_completion/results/matching_strata/anchored_matching_strata.json)

### Layer 7: Matching branch — stratum closures

#### k=7 (6/6 closed, verified)
- idx32,37: direct residual-negative Wang rows
- idx33,34: explicit clique-cover certificates (independently checked)
- idx35,36: graph independent-set CNFs, CaDiCaL UNSAT, drat-trim verified
- Source: `workspace/data/graph_cert/k7_rerun/`
- Manifest: [k7_unified_manifest.json](../results/k7_manifest/k7_unified_manifest.json)

#### k=6 (5/10 closed; 5 in progress)
- idx22,23,24,28: analysis clique-cover certificates
- idx25: analysis iterative separation, 5 rounds, DRAT verified
- idx26,27,29,30,31: iterative separation IN PROGRESS (batch s33_t20_tool1)
- Source: `workspace/data/graph_cert/k6_color_pilot/`, `smoke/idx25/`

#### k=5 (0/10 in progress)
- All 10 strata: iterative separation IN PROGRESS (batch s33_t21_tool1)

#### k=4 (0/7 in progress)
- All 7 strata: iterative separation IN PROGRESS (batch s33_t22_tool1)

#### k=3,2,1 (0/5 in progress)
- All 5 strata: iterative separation IN PROGRESS (batch s33_t23_tool1)

### Layer 8: Adjacent-pair (rep2) branch
- Fixed prefix: {E11, E12} = {1, 2}
- Survivors: 509 candidates, target: 18
- Stabilizer: |Stab({E11,E12})| = 192, creating 17 orbits on candidates
- Current status: iterative separation IN PROGRESS (batch s33_t24_tool1)
- No residual-0 vertex exclusions (max lb for rows containing both = 17)
- 11,280 residual-1 edges, density 8.7%
- Base graph IS has α ≥ 18 (greedy found size-18 IS with 3,441 full-LUT violations)

### Layer 9: Conclusion
If Layers 7-8 all close with independently verifiable DRAT proofs:
- No length-20 decomposition exists over F_2
- Combined with Wang lb 20: R_{F_2}(T) ≥ 21

## Scope and Limitations
- This proves R_{F_2} ≥ 21, NOT R_Q ≥ 21 or R_C ≥ 21
- Integer algorithms can be reduced mod 2: R_{F_2} ≤ R_Z ≤ R_Q
  So R_{F_2} ≥ 21 means no length-20 INTEGER algorithm exists
- But rational algorithms with denominators might still have rank ≤ 20
- A rank-23 optimality proof over Q or R requires additional work

## Dependencies Requiring Independent Verification
1. Wang certificate correctness (replay verified)
2. Complete LUT computation (Gaussian-binomial count verified)
3. Multiplicity-free scan (511 rows checked)
4. Rank-1 existence DRAT proofs (independently checked)
5. Global cover argument (mathematical + code verification)
6. Orbit enumeration completeness (13,327 matchings, 38 strata)
7. Each stratum closure artifact (DRAT + provenance + regeneration)
8. Group action conventions (row-major encoding, action formula)
9. LUT symmetry under the group (same rows after action)
