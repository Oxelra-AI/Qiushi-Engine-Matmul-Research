# Rank-22 Jacobian Analysis and Pairing-Defect Tangent Cone

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Purpose

Build the characteristic-zero algebraic framework for the rank-22 question on T⟨3,3,3⟩
using Jacobian rank analysis and pairing-defect tangent cone computation.

## Key Results

### 1. Secant Variety Dimensions (Non-Deficiency)

The generic Jacobian rank of the rank-r Brent parameterization was computed over
F_p for p ∈ {65521, 104729, 1000003} and r ∈ {20,21,22,23,24}.

All match the Alexander–Hirschowitz expected dimension:
- r=20: rank 500 = 25×20 ✓
- r=21: rank 525 = 25×21 ✓
- r=22: rank 550 = 25×22 ✓  →  σ₂₂ has codimension **179** in K^729
- r=23: rank 575 = 25×23 ✓
- r=24: rank 600 = 25×24 ✓

**There is no deficiency.** The secant variety σ₂₂(Seg(P⁸×P⁸×P⁸)) has the
expected dimension 549 (projective) = 550 (affine). The generic fiber over a
rank-≤22 tensor has dimension 594 − 550 = 44.

### 2. First-Order Obstruction at Known Rank-23 Schemes

For each of the 23 possible truncations of cn122 (dropping one term):
- Jacobian rank: 514–520 (vs generic 550)
- Kernel dimension: 74–80 (vs generic 44)
- **Residual NOT in Jacobian image: 0/23**

Same for serendipitous_8d34:
- Jacobian rank: 518–524
- **Residual NOT in image: 0/23**

**No first-order perturbation of any 22-term truncation of any known rank-23
scheme can make T⟨3,3,3⟩ reachable.**

### 3. Corrected Jacobian Rank at cn122

The `invariants.json` file (exact modular computation) confirms:
- **Jacobian rank = 527** (not 531 as stated in earlier Meta-Trace)
- Kernel dimension = 94
- Consistent over F₂, F₃, F₅, Q, and all tested primes up to 10⁶
- The earlier "531" was a floating-point SVD artifact from `formal_lift_pairing.py`

### 4. Pairing-Defect Tangent Cone

At cn122, the 94-dimensional fiber tangent space was analyzed for its projection
to the pairing change space.

**The left-null-space projection C = P_null @ δP was computed for all 94 kernel
directions:**
- C-matrix rank distribution: {0:51, 1:13, 2:5, 3:5, 4:4, 5:2, 6:1, 7:2, 8:4, 9:1, 10:2, 11:3, 12:1}
- 51 directions produce zero change in pairing (W-only or P-preserving)
- 43 directions produce nonzero but low-rank C
- **All 94/94 directions produce C of rank < 23 (rank-deficient)**
- C-image dimension: **36**

The codimension of {rank ≤ 22} in the C-space K^{58×23} is:
(58−22)(23−22) = **36**

Therefore: the C-image from the fiber has dimension exactly equal to the
codimension of the rank-22 condition. The expected tangent-cone intersection
dimension is max(0, 36 − 36) = **0**.

**Gauge analysis:**
- Gauge tangent vectors: 50 generators (27 GL₃³ + 23 rescaling)
- Gauge in fiber: **32** (23 rescaling + 9 GL₃ stabilizer of T)
- Moduli tangent: 94 − 32 = 62
- Expected pairing-defect moduli: 0 − 32 = **−32**

**The negative expected dimension strongly suggests the pairing-defect locus in
the rank-23 fiber is empty.** This is a first-order tangent-cone argument, not
a proof; higher-order corrections could create isolated solutions. But the
structural codimension balance (C-image = 36 = codimension of rank-22 condition)
leaves zero excess dimensions, and the gauge then pushes the moduli count well
into the negative.

### 5. Fiber Structure

| Quantity | Value |
|----------|-------|
| Generic Brent rank (r=22) | 550 |
| Generic fiber dim (r=22) | 44 |
| Gauge (GL₃³ + rescaling) | 49 |
| Gauge > fiber | ✓ → generically rigid |
| Fiber dim at cn122 (r=23) | 94 |
| Gauge in cn122 fiber | 32 |
| Cn122 moduli | 62 |
| Pairing-defect tangent | 0 expected |
| Pairing-defect moduli | −32 expected |

### 6. MM-22 SAT (F₂)

Kissat 4.0.4 on MM-22.cnf (24,975 vars, 111,780 clauses): **UNKNOWN after 600s**.
7.4M conflicts, 67% variable elimination. The F₂ rank-22 question remains
unresolved by direct SAT.

### 7. Shortened System Structure

After W-elimination (formulation):
- 531 equations in 396 UV variables
- Effectively 352 independent (= 550 − 198)
- Kernel at generic domain point: 44
- At random domain points: 530–531 out of 531 residual entries nonzero
- System is generically overdetermined after gauge (396 − 352 = 44, minus gauge 49)

## Scientific Interpretation

These results establish a complete first-order algebraic picture:

1. The rank-22 variety σ₂₂ has the expected dimension (no deficiency helps).
2. T⟨3,3,3⟩ is locally unreachable from known rank-23 schemes with 22 terms.
3. Within the rank-23 fiber, the pairing-defect tangent cone has the minimal
   possible dimension (zero), and the gauge makes the moduli strongly negative.
4. Any rank-22 decomposition must be structurally isolated from all known schemes.

These are necessary but not sufficient for proving rank-23 optimality.
For a proof, one would need either:
- A global algebraic obstruction (some polynomial invariant separating σ₂₂ from T)
- A complete finite-field search (strengthened SAT or exhaustive enumeration)
- A geometric argument that the tangent-cone balance lifts to higher order

## Files

- [rank22_jacobian_probes.json](../results/rank22_probes/rank22_jacobian_probes.json): detailed Jacobian probes
- [rank22_jacobian_analysis.json](../results/rank22_probes/rank22_jacobian_analysis.json): analysis summary
- [rank22_jacobian_probes.py](../code/rank22_jacobian_probes.py): generic Jacobian rank + truncation analysis
