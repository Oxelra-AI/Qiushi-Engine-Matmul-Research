# Synthesis: E11 Core Structure, Route Analysis, and Mathematical Mechanisms

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## research research_record — Explore Phase

---

## correction notice

Several analysis bridge statements below have been superseded by the analysis correction in [e11_bridge_reconstruction.md](e11_bridge_reconstruction.md) and [corrected_bridge_and_tight_geometry.md](corrected_bridge_and_tight_geometry.md).

The corrected inherited bridge is: the old no-rank-one-support certificates exclude full length-20 A-supports with **no** rank-one factor, so a hypothetical length-20 full decomposition must contain one rank-one A-factor. Normalize it to E11 and quotient it away; exactly nineteen nonzero E11-core terms remain. The repeated-projected-A certificate applies to these nineteen terms. For a normalized rank-20 full decomposition the residual condition is rank$(M_0+\sum_{\varepsilon_t=1}X_t)\le1$, not residual zero. A residual-zero equation belongs only to a different bookkeeping setup without the selected E11 rank-one term. The low-dimensional Koszul flattening maps also have an a priori lower-bound ceiling of 15 and should not be treated as a promising way to reach 18--19 for this core.

## Key Findings (This ARTIFACT)

### 1. Core Tensor Block Structure (Computed and Verified)
The E11 core T_core ∈ F₂⁸ ⊗ F₂⁹ ⊗ F₂⁹ has **8 slices, each being I₃ in a specific 3×3 block** of the 9×9 B⊗C matrix. The 9 blocks form a 3×3 grid:
- Core occupies 8 blocks: (2,1),(3,1),(1,2),(2,2),(3,2),(1,3),(2,3),(3,3)
- M₀ = I₃ occupies block (1,1)
- **All 9 slices have completely disjoint support** (no shared nonzero entries)

The core's slice space is V = {Λ ⊗ I₃ : Λ ∈ L} where L = {Λ ∈ M₃(F₂) : Λ₁₁ = 0}, an 8-dimensional subspace of M₉(F₂). [review-corrected: not a simple punctured Kronecker product]

### 2. Inner Product Rank Condition (Proved)
Over F₂: **rank(I₃ + bc^T) = 2 iff b·c = 1, and rank(I₃ + bc^T) = 3 iff b·c = 0**.
Proof: matrix determinant lemma gives det(I₃ + bc^T) = 1 + c^T b. Also rank(I₃ + bc^T) ≥ rank(I₃) - rank(bc^T) ≥ 2. Confirmed by exhaustive computation over all 49 rank-one 3×3 matrices.

**Consequence**: 28/49 rank-one perturbations reduce I₃ from rank 3 to 2; 21/49 keep it at 3. No single perturbation reaches rank ≤ 1.

### 3. Cross-Contamination Constraint (Identified)
A rank-one 9×9 matrix spanning multiple 3×3 blocks creates **cross-contamination** in every assigned core slice. For block support rectangle P_t × Q_t where |P_t|=a, |Q_t|=b, the term contributes to all a×b blocks.

**Cross-contamination does not prohibit sharing** (review-corrected), but requires **exact cancellation** in ALL non-target blocks of every slice. The cancellation is a system of zero-sum matrix equations over F₂, not an automatic consequence. The savings arithmetic Σ(m_t - 1) ≥ 5 is a necessary counting condition but NOT sufficient — it ignores cancellation costs.

### 4. Core Rank Bounds
```
17 ≤ R_F₂(T_core) ≤ 21
```
- Lower: from R(T) ≥ 20 and R(T_core) ≥ R(T) - 3
- Upper: cn122 rank-23 scheme gives 21-term core decomposition over F₂
  (19 distinct projected A-directions including zero; 4 repeated-direction pairs)
- Flattening bound: only 9 (far too weak)

### 5. Residual Condition (analysis corrected)
For the normalized lower-bound bridge, one full rank-20 term has A-factor E11 and disappears after quotienting. The remaining nineteen terms form the core. With lift bits ε_t on those nineteen terms, the deleted slice equation is
\[
b_0c_0^T+\sum_{\varepsilon_t=1}X_t=M_0,
\]
so the exact lift condition for a full rank-20 decomposition is
\[
\operatorname{rank}(M_0+\sum_{\varepsilon_t=1}X_t)\le1.
\]
Residual zero is not the normalized bridge condition; it applies only to a formulation in which lifted core terms alone cover the deleted slice without the selected E11 rank-one term.

Consequences:
- excluding every exact 19-term E11 core proves the full lower bound ≥21;
- excluding every exact 19-term E11 core that admits the rank-≤1 lift residual also proves the full lower bound ≥21;
- constructing any exact 19-term E11 core proves the upper bound ≤22 by adding the three deleted-slice terms.

### 6. Rank-Weight Inequalities (review)
For any rank-r core decomposition with A-labels producing linear forms ℓ_t, define S_Λ = {t : ℓ_t(Λ) = 1}. Then:
```
|S_Λ| ≥ 3 · rank(Λ)   for all nonzero Λ ∈ L
```
This is a family of 255 necessary conditions on the coefficient code.

### 7. I₃ Decomposition Count
Over F₂: exactly **28 distinct unordered triples** of rank-one 3×3 matrices sum to I₃.
These can be organized as Fano-frame types. 55.6% of decomposition pairs share 1 b-factor; 33.3% share 2.

---

## Route Comparison

### Route A: Upper Bound (R(T) ≤ 22 via rank-19 core)

**Goal**: Construct 19 rank-one 9×9 matrices and F₂⁸ labels decomposing T_core.

**Most promising approaches** (from review):
1. **Hadamard rectangle encoding**: Formulate as syndrome-rectangle problem with coefficient code. 81 Hadamard products of B and C rows must fall in prescribed cosets. Clean exact model.
2. **Fano-frame + rectangle corner cancellation**: Choose frame types for each block and solve the global cancellation system.
3. **cn122 modification**: Find switch identities to change A-direction collision pattern, or find a new rank-23 scheme with better F₂ core structure.
4. **Punctured Kronecker / algorithm splicing**: Block-decompose A=(0,u;v,M), B=(r;N) and splice sub-algorithms for uN and vr+MN.

**Key obstacle**: Cross-contamination requires exact cancellation. Not a simple covering problem.

### Route B: Lower Bound (R(T) ≥ 21)

**Goal**: Exclude all valid 20-distinct-direction core decompositions (possibly with residual analysis).

**Most promising approaches**:
1. **Complete Wang E11 occupation** (417,198 rows): SAT/CP-SAT with structural constraints. Old attempts returned UNKNOWN in 20min.
2. **Tight contraction/factor-domain geometry**: Use contractions with active count exactly equal to matrix rank to force B/C factors into column and row spaces, then combine with complete Wang rows, independent-transversal tests, residual rank-≤1 lifting, and exact fixed-A rank-one completion. analysis found this can strongly restrict nearby rank-weight supports, while scalar rank-weight alone is too weak.
3. **Coding theory / rank-weight + Plücker**: Coefficient code must satisfy 255 rank-weight inequalities plus Grassmann-Plücker relations. Enumerate viable codes then check Hadamard syndrome feasibility.
4. **Inner-dimension recursion**: Prove substitution lemma R(core_m) ≥ R(core_{m-1}) + t_m.
5. **Capacity-rectangle defect**: New mechanism — prove any 19-term system has insufficient "defect budget" for cancellation.

---

## Open Mathematical Questions (Refined)

**Q1 (Upper bound)**: Does R_F₂(T_core) ≤ 19?
→ Equivalent to: can 19 rank-one 9×9 matrices solve the Hadamard syndrome-rectangle system?

**Q2 (Lower bound, strong)**: Does R_F₂(T_core) ≥ 21?
→ Would directly imply R_F₂(T) ≥ 21.

**Q3 (Lower bound, intermediate)**: Can every exact 19-term E11 core with a rank-≤1 residual lift be excluded?
→ Would also imply R_F₂(T) ≥ 21, and is weaker than excluding all 19-term cores.

**Q4 (Factor geometry)**: Which complete-Wang-admissible or near-admissible A-supports have tight rank-1/rank-2 contractions that impose nontrivial B/C domains while still passing the fixed-domain linear test?
→ This is the useful refinement of the rank-weight viewpoint; scalar rank-weight support enumeration alone does not add enough leverage.

---

## Recommended Next Work

1. **Search fixed-A surfaces with complete Wang plus tight-domain leverage**: optimize for zero complete-Wang violations and for tight rank-1/rank-2 contractions that constrain B/C factors without creating zero-domain or linear-membership contradictions.

2. **Run exact fixed-A rank-one completion on any support that survives complete Wang and tight-domain tests**; a verified completion gives a 19-term E11 core and hence a full rank-≤22 algorithm.

3. **Develop the residual rank-≤1 lift obstruction with valid algebraic consequences**: use saturation or rank/count hypotheses before forcing per-term B/C alignment, and coordinate with research_record on this lower-bound route.

4. **Continue analyzing the cn122 21-term core as a positive control** for domain computations and possible local transformations, while remembering it is not a rank-19 construction.

---

## Files Created in This ARTIFACT
- [e11_bridge_reconstruction.md](e11_bridge_reconstruction.md) — full mathematical bridge
- [synthesis.md](synthesis.md) — this synthesis
- [core_tensor_analysis.py](../code/core_tensor_analysis.py) — tensor construction, flattenings, rank-23 analysis
- [core_block_analysis.py](../code/core_block_analysis.py) — I₃ decompositions, sharing statistics
- [cross_contamination_analysis.py](../code/cross_contamination_analysis.py) — contamination verification, bounds
- `workspace/data/core_analysis/` — saved tensors and results
- `independent-verification-record` — review branch outputs
