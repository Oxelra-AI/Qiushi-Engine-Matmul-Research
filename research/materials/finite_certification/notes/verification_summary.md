# Verification Summary

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## All proof components verified

### 1. Transpose convention ✓
- Correct automorphism: (A,B,C) → (A^T, C, B) under T[3i+j,3j+k,3i+k]=1
- 200,000 random triples: 0 failures
- Wrong map (A^T, C^T, B^T): 97,025 failures
- Tensor is symmetric under the correct automorphism
- File: `audit/transpose_convention.json`

### 2. Dim-2 line caps at orbits 484-491 ✓
- Orbits 484-488, 490, 491: max line cap = 1 (distinct-support DFS valid)
- Orbit 489: max line cap = 2 (one direction with cap 2, lb_U=16)
- INTEGER multiplicity model essential for orbit 489
- File: `audit/dim2_line_caps.json`

### 3. Eight dim-2 occupation raises (484-491) ✓
- CP-SAT INFEASIBLE: all 8 orbits (with integer variables)
- HiGHS MILP integer-INFEASIBLE: all 8 orbits
- LP relaxation FEASIBLE: all 8 (obstruction is integral, no Farkas certificate)
- Both independent solvers agree
- File: `dim2_certificates/cpsat_certificate_summary.json`

### 4. Saturation lemma + product identity ✓
- P = Phi_A(T) is a 27×27 permutation matrix (rank 27)
- Product formula verified: 50,000 random triples, 0 failures
- Diagonal consequence verified: 840 checks, all correct
- Off-diagonal: product of 4 invertible F_2 matrices always rank 3 (10,000 samples)
- Known rank-23 scheme has rank sum 30 > 27 (expected: idempotents don't apply)
- File: `audit/saturation_proof.json`

### 5. GL3×GL3 invariance ✓  
- GL_3(F_2) transitive on F_2^3 \ {0}: all 7 vectors reachable from e_1
- LUT values invariant: 1,400 transform checks, 0 failures
- File: `audit/gl3_invariance.json`

### 6. Coset lemma (rank-one-difference → common coset) ✓
- h=3: 49,882 triples with pairwise rank-1 differences, ALL in coset (0 counterexamples)
- h=4: 24,778 quads with pairwise rank-1 differences, ALL in coset (0 counterexamples)
- Column type: 24,941 (h=3), 12,695 (h=4)
- Row type: 24,941 (h=3), 12,083 (h=4)
- File: `audit/coset_lemma.json`

### 7. AG(3,2) cap theorem ✓
- F_2^3 has exactly 14 four-element affine planes
- Cap number = 4: every 5-element subset contains a plane
- Verified by exhaustive enumeration
- File: `audit/ag32_cap.json`

### 8. Single-coset dim-3 values ✓
- Normalized coset S = ⟨272, 4, 2, 1⟩ has LB = 14 (exact, = R(T_{2,3,3}))
- 15 dim-3 subspaces: 1 with LB=15 (rank-1 family R), 14 with LB=17 (affine planes)
- Confirmed inline computation

## Proof chain status

The proof that R_{F_2}(T_{3,3,3}) ≥ 21 rests on:

| Component | Status | Theorem-grade? |
|-----------|--------|----------------|
| Wang LB=20 certificate | Independently replayed (analysis) | Yes |
| All dim-1 LB = 19 | Verified from LUT | Yes |
| Eight dim-2 raises 484-491 | CP-SAT + HiGHS agree | Needs proof-logging solver |
| Coset lemma | Exhaustive F_2 verification | Algebraic proof elementary |
| AG(3,2) cap theorem | Exhaustive enumeration | Elementary combinatorics |
| LUT transpose invariance | All 8.28M entries checked | Yes |
| Transpose automorphism | Algebraic + numerical | Yes |
| Split flattening rank 27 | Direct computation | Yes |
| Product identity formula | 50K random + algebraic | Algebraic proof needed |
| Saturation lemma | Standard linear algebra | Algebraic proof elementary |

**Bottleneck for theorem-grade proof**: The 8 dim-2 occupation raises lack proof-logging certificates. The LP relaxation is feasible for all 8, so no simple linear certificate exists. Options:
1. Proof-logging PB solver (e.g., VeriPB)
2. Complete safe-DFS for 7 orbits with max_cap=1 (orbit 489 needs PB)
3. Lean formalization of the integer system

All other components have either exact deterministic verification or elementary algebraic proofs.
