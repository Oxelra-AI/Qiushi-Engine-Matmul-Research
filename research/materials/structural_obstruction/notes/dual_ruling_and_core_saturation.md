# Dual ruling-line shared-factor constraints and corrected core saturation

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Key findings

### 1. Dual ruling-line shared-factor constraint family

**Mathematical basis**: For T⟨3,3,3⟩ over F₂, the contraction L(Q) = Q^T ⊗ I₃.
For rank-1 Q = uv^T: col(L(Q)) = ⟨v⟩ ⊗ F₂³, row(L(Q)) = ⟨u⟩ ⊗ F₂³.
Two distinct rank-1 contractions Q₁ ≠ Q₂ both saturated (w=3) forces
their participating term sets I_{Q₁} ∩ I_{Q₂} = ∅ (from disjoint row or
column spaces).

On a **dual ruling line** {Q₁, Q₂, Q₃=Q₁+Q₂} (all rank-1, sharing u or v):
  w(Q_j) = 3 AND w(Q_k) = 3  ⟹  w(Q_l) = 6   (cyclic)

This gives **294 model constraints** from 98 dual ruling lines × 3 pairs.

**Validated on cn122 mod 2**: PASS (0 ruling-line violations).
analysis contraction-lower-none support: **1 VIOLATED ruling line** (exactly
the {q=1, q=65, q=64} triple from the zero C-domain certificate).

**Computational result**: adding dual ruling-line constraints to rep2 CP-SAT
does not strongly cut because the solver avoids saturation (choosing w≥4
for all rank-1 contractions). The constraints are mathematically correct
but not computationally decisive for this encoding.

### 2. Combined rep2 separation model

Combined Wang upper + contraction lower + primal ruling + dual ruling +
all5 orbit tiers + iterative zero-domain cuts.

Round 0 support: 533 violations, **linear test PASSES** (affine_dim=549),
**no zero-domain terms**, 20 saturated contractions, domain hist {B6_C3:6, B6_C6:4, B9_C9:10}.
Round 1: UNKNOWN after 212s.

This is the strongest single-round support found: passes saturation
completely, fails only on complete-LUT Wang violations.

### 3. Core contraction computation corrected

**Critical bug found**: the F₂ linear contraction L(q) = ⊕_{j: bit_j(q)=1} T[e_j]
(XOR of basis-element slices), NOT the sum over the affine hyperplane
{a: ⟨q,a⟩=1}. The hyperplane sum gives all-zero contractions due to
characteristic-2 cancellation (each entry is the sum of 2^{dim-1} terms ≡ 0 mod 2).

**Corrected rank distribution for E11 core**: {3: 33, 6: 150, 9: 72}.
This gives 255 contraction lower bounds for the core search.

### 4. Core saturation search results

Corrected search through 10 rounds, 15 supports examined:
- Rounds 1 and 5 found **saturation-clean** supports (zero-domain count = 0)
  but with 226 and 97 Wang violations respectively
- Rounds 0,2,3,4,6,7,8 found supports with 2-7 zero-domain terms
- Round 9: UNKNOWN after 120s

Round-5 saturation-clean support (97 Wang violations):
[3, 4, 5, 7, 8, 9, 28, 36, 64, 65, 130, 144, 146, 162, 195, 216, 219, 249, 255]

### 5. cn122 core validation issue

cn122 restricted to E11 core has only 8 unique projected A-factors (from 10
terms with a_{00}=0). The saturation mechanism gives 222 undersaturated
contractions and all 8 terms with zero B AND C domains. This is because
the cn122 core uses 10 terms (with 2 repetitions) from 8 projective points
in a 255-point space, and the rank-19 contraction lower bounds require
at least 3 terms per contraction while 8 points can't cover enough.

This validates that the saturation mechanism correctly rejects a support
too small for the target rank, but also shows that the cn122 core restriction
at 8 unique points is far from rank 19.

## Key files

- [dual_ruling_shared_factor.py](../../quotient_cores/code/dual_ruling_shared_factor.py) - dual Segre structure and validation
- [combined_rep2_separation.py](../../quotient_cores/code/combined_rep2_separation.py) - combined rep2 model
- [core_e11_saturation_v2.py](../code/core_e11_saturation_v2.py) - corrected core search
- [dual_segre_structure.json](../../quotient_cores/results/dual_ruling/dual_segre_structure.json) - 49 rank-1 contractions, 98 lines
- [combined_sep_all5.json](../../quotient_cores/results/dual_ruling/combined_sep_all5.json) - rep2 combined result
- [core_e11_saturation_v2.json](../results/dual_ruling/core_e11_saturation_v2.json) - core search result
- Background task `s43_t32_tool1`: long core search (40 rounds, 300s/round)

## Research state

- R_F2 lower bound remains 20 (Wang); no R_F2 ≥ 21 proof
- No rank-≤22 algorithm found
- Matching closures: 16/38 closed; 22 open; rep2 open
- The saturation mechanism is informative for the full tensor and the corrected
  core, but the complete-LUT Wang system remains the binding constraint
- The most promising route toward rank ≤ 22 is finding a Wang-admissible
  saturation-clean rank-19 core A-support, then solving the rank-one completion
