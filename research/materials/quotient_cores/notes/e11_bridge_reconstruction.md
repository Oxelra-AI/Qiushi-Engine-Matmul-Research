# E11 Quotient Core: Mathematical Bridge and Structural Analysis

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## research research_record, analysis

---

## 1. Tensor Convention

Work over $\mathbb F_2$. The 3×3 matrix multiplication tensor is
$$T = T_{\langle3,3,3\rangle} = \sum_{i,j,k=1}^{3} e_{ik} \otimes e_{kj} \otimes e_{ij} \;\in\; \mathbb F_2^9 \otimes \mathbb F_2^9 \otimes \mathbb F_2^9$$
where $e_{ij}$ denotes the elementary matrix with a 1 in position $(i,j)$.
Index convention: $e_{ij} \mapsto 3(i-1)+(j-1)$, so $e_{11}=0,\ldots,e_{33}=8$.

The tensor $T$ encodes the bilinear map $(A,B)\mapsto AB$ for $3\times3$ matrices over $\mathbb F_2$. Its trilinear form is $T(A,B,C) = \mathrm{tr}(C^T AB)$.

$T$ has exactly 27 nonzero entries, one for each triple $(i,j,k)$.

## 2. Known Frontier

Over $\mathbb F_2$:
$$20 \le R_{\mathbb F_2}(T) \le 23.$$

- **Lower bound 20**: Wang's certificate (arXiv:2603.07280), independently replay-verified in research_record analysis. Certificate SHA256 `25595a88...`.
- **Upper bound 23**: cn122 rank-23 integer scheme, verified in research_record analysis over both Python and native backends. Scheme SHA256 `47fa58e6...`.

## 3. E11 Quotient Core Construction

**Definition.** Let $E_{11} = e_{11}$ be the rank-one matrix with a 1 at position $(1,1)$. The **E11 quotient projection** is
$$\pi: \mathbb F_2^9 \to \mathbb F_2^9/\langle E_{11}\rangle \cong \mathbb F_2^8$$
which projects out the $E_{11}$ component of the A-factor.

The **E11 core tensor** is:
$$T_{\rm core} = (\pi \otimes \mathrm{id} \otimes \mathrm{id})(T) \;\in\; \mathbb F_2^8 \otimes \mathbb F_2^9 \otimes \mathbb F_2^9$$

Concretely, $T_{\rm core} = T[1{:},:,:]$ in the standard basis ordering — the 8 slices of $T$ corresponding to $A$-directions $e_{12},e_{13},e_{21},\ldots,e_{33}$.

The **deleted E11 slice** is:
$$M_0 = T(e_{11}^*,\cdot,\cdot) = \sum_{j=1}^3 e_{1j} \otimes e_{1j}$$
which is the rank-3 partial-permutation matrix with 1s at positions $(0,0),(1,1),(2,2)$. Equivalently, $M_0 = I_3$ in the (1,1)-block of the $3\times3$ block decomposition of $9\times9$ matrices.

## 4. Block Structure (Computed, analysis; convention verified analysis)

**Convention note (analysis):** The contraction matrix is $M_\lambda = \Lambda^T \otimes I_3$ (not $\Lambda \otimes I_3$). This means A-entry $(i,j)$ maps to B$\otimes$C block $(j,i)$. The block table below uses 1-indexed blocks and is correct. Scripts in `coupled_dual_basis_system.py` and `shadow_system_analysis.py` use the corrected convention. Earlier analysis scripts (`core_tensor_analysis.py`, `core_block_analysis.py`, `cross_contamination_analysis.py`) used the uncorrected convention and should not be reused without updating the block assignment.

The $9\times9$ $B\otimes C$ matrix space decomposes into $3\times3$ blocks indexed by $(B\text{-block},C\text{-block})$ where B-block $k=\{e_{k1},e_{k2},e_{k3}\}$ and C-block $i=\{e_{i1},e_{i2},e_{i3}\}$.

**Each core slice is a $3\times3$ identity matrix $I_3$ in a specific block:**

| Core A-direction $\bar e_{ik}$ | B-block | C-block | Slice content |
|------|---------|---------|---------------|
| $\bar e_{12}$ | 2 | 1 | $I_3$ in block $(2,1)$ |
| $\bar e_{13}$ | 3 | 1 | $I_3$ in block $(3,1)$ |
| $\bar e_{21}$ | 1 | 2 | $I_3$ in block $(1,2)$ |
| $\bar e_{22}$ | 2 | 2 | $I_3$ in block $(2,2)$ |
| $\bar e_{23}$ | 3 | 2 | $I_3$ in block $(3,2)$ |
| $\bar e_{31}$ | 1 | 3 | $I_3$ in block $(1,3)$ |
| $\bar e_{32}$ | 2 | 3 | $I_3$ in block $(2,3)$ |
| $\bar e_{33}$ | 3 | 3 | $I_3$ in block $(3,3)$ |

$M_0$ occupies the missing block $(1,1)$ with content $I_3$.

**All 9 slices have completely disjoint support.** No two slices share a nonzero entry.

## 5. Upper Bound Bridge

**Theorem.** $R_{\mathbb F_2}(T) \le R_{\mathbb F_2}(T_{\rm core}) + 3$.

*Proof.* Given a rank-$r$ decomposition $T_{\rm core} = \sum_{t=1}^r \bar a_t \otimes X_t$, lift each $\bar a_t$ to $a_t = \tilde a_t \in \mathbb F_2^9$ with zero $E_{11}$-component. Then:
$$T - \sum_{t=1}^r a_t \otimes X_t = e_{11} \otimes M_0$$
which has rank $\le \mathrm{rank}(M_0) = 3$. Hence $R(T) \le r + 3$. $\square$

**Corollary.** If $R_{\mathbb F_2}(T_{\rm core}) \le 19$, then $R_{\mathbb F_2}(T) \le 22$.

**Refined lift formula.** For any core decomposition with lift bits $\varepsilon_t \in \mathbb F_2$ (setting $a_t = \tilde a_t + \varepsilon_t e_{11}$):
$$R_{\mathbb F_2}(T) \le r + \mathrm{rank}\!\left(M_0 + \sum_{t:\varepsilon_t=1} X_t\right)$$
Taking $\varepsilon = 0$ gives the $r+3$ bound. A better lift gives a tighter bound.

## 6. Lower Bound Bridge (analysis corrected)

**Correction.** The analysis wording reversed the inherited Wang-occupation implication. The earlier research analysis bridge says that proof-producing T-level Wang branches exclude length-20 supports with **no** rank-one A-factor. Thus every hypothetical length-20 decomposition of the full tensor has at least one rank-one A-factor. This section supersedes the incorrect analysis wording.

**Setup.** Suppose a decomposition of $T$ of length at most 20 exists. Wang's verified lower bound gives length exactly 20. Let
$$T=\sum_{t=0}^{19} a_t\otimes b_t\otimes c_t.$$
The inherited no-rank-one-support certificates imply at least one $a_t$ is a nonzero rank-one $3\times3$ matrix. By the matrix-multiplication tensor symmetry, normalize that factor to $a_0=E_{11}$.

The one-dimensional Wang row for $\langle E_{11}\rangle$ has lower bound 19 at length 20, hence capacity one: at most one projective A-factor can lie in $\langle E_{11}\rangle$. Therefore after quotienting the A-slot by $\langle E_{11}\rangle$, the normalized term disappears and the other 19 terms have nonzero projected A-factors. They form a length-19 E11-core decomposition
$$
T_{\rm core}=\sum_{t=1}^{19}\bar a_t\otimes X_t,\qquad X_t=b_t c_t^T.
$$
The analysis repeated-projected-A certificate applies to these nineteen quotient terms: if a rank-19 E11-core support satisfying the complete Wang occupation table repeats a projected direction, that branch is excluded by the compact CNF/DRAT object reviewed in earlier research analysis. After those inherited certificates are replayed for earlier research theorem use, the remaining lower-bound branch is the distinct length-19 E11 core.

**Consequences.**

- If every length-19 E11-core decomposition is excluded, then no full length-20 decomposition exists and $R_{\mathbb F_2}(T)\ge21$.
- A more refined lower-bound route may instead exclude only those exact length-19 E11-core decompositions whose lifts satisfy the residual rank-$\le1$ condition in §9; this is enough to exclude full rank 20.
- Conversely, any exact length-19 E11-core decomposition gives the desired upper bound $R_{\mathbb F_2}(T)\le22$ by adding three rank-one terms for the deleted E11 slice, independent of whether it admits a rank-20 lift.

## 7. Flattening Ranks (Computed)

| Tensor | A-flat rank | B-flat rank | C-flat rank | Lower bound |
|--------|-------------|-------------|-------------|-------------|
| $T$ (full) | 9 | 9 | 9 | 9 |
| $T_{\rm core}$ | 8 | 9 | 9 | 9 |

These are weak compared to the target 19–20. The flattening lower bound of 9 for the core shows that naive linear-algebraic arguments cannot settle the rank-19 question.

## 8. I₃ Decomposition Flexibility (Computed)

Over $\mathbb F_2$, there are exactly **28 distinct unordered triples** of rank-one $3\times3$ matrices summing to $I_3$.

This is the local flexibility: each core block can use any of 28 different rank-one decompositions. For block sharing, two blocks in the same B-row or C-column can share a factor if their decompositions have a common b-vector (resp. c-vector).

**Sharing statistics (all 378 decomposition pairs):**
- 55.6% share 1 b-factor
- 33.3% share 2 b-factors
- 0% share all 3 b-factors (same for c-factors)

## 9. Residual Rank Condition (Critical Finding, review-Corrected)

**Proposition (computed, analysis).** Over $\mathbb F_2$, for every rank-one $3\times3$ matrix $X$:
$$\mathrm{rank}(I_3 + X) \ge 2.$$
No single rank-one perturbation reduces $I_3$ below rank 2.

Two rank-one perturbations CAN achieve rank 1: $I_3 + e_1e_1^T + e_2e_2^T = e_3e_3^T$ (rank 1).
Three can achieve rank 0: $I_3 + e_1e_1^T + e_2e_2^T + e_3e_3^T = 0$.

**Correct residual distinction after normalizing a rank-one A-factor.**

For the normalized full rank-20 bridge of §6, the selected term is $E_{11}\otimes b_0c_0^T$ and the other nineteen terms decompose the core. Writing $\varepsilon_t$ for the E11 lift bit of the nineteen core terms, the deleted-slice equation is
$$
b_0c_0^T+\sum_{t:\varepsilon_t=1}X_t=M_0.
$$
Equivalently,
$$
\operatorname{rank}\!\left(M_0+\sum_{t:\varepsilon_t=1}X_t\right)\le1.
$$
This rank-$\le1$ condition is the correct lift obstruction for excluding full rank 20 through the normalized E11 bridge.

A residual-zero condition applies only to the different bookkeeping problem in which the lifted core terms alone cover the deleted slice with no extra E11 rank-one term. It is not the condition for the normalized length-20 lower-bound bridge.

The global rank-$\le1$ constraint couples the $(1,1)$ block with all other blocks: each selected $X_t$ that contributes to $(1,1)$ may also contribute to core blocks, and the final residual must be a single rank-one $9\times9$ matrix (or zero).

**Consequence for the lower-bound bridge:** excluding arbitrary twenty-term core projections is not the inherited route. The load-bearing target is a nineteen-term E11 core together with possible lift bits whose residual has rank at most one. Excluding all nineteen-term cores is stronger and sufficient; constructing one gives the rank-$\le22$ upper-bound route.

## 10. Rank-23 Scheme over F₂ (Computed)

The cn122 rank-23 scheme, reduced mod 2:
- All 23 terms survive (nonzero over $\mathbb F_2$)
- **19 distinct projected A-directions** (including 2 terms with zero projection = pure $E_{11}$)
- **4 repeated-direction pairs**: zero, $\bar e_{33}$, $\bar e_{13}+\bar e_{23}$, $\bar e_{31}$
- Each merged pair has rank 2 (not rank 1)
- **Core decomposition from scheme: 21 terms** (not 19)
- Weight distribution: 9 weight-1, 4 weight-2, 2 weight-3, 3 weight-4, 1 each weight 5,6,7

The scheme does NOT give a rank-19 core decomposition. To achieve rank $\le 22$, we need to find a better core decomposition with 5 fewer terms than the current 24-term naive bound.

## 11. Savings Arithmetic

Naive bound: 8 slices × 3 rank-one terms each = 24 terms.
Target: 19 terms → need to save 5 terms through cross-block sharing.

A rank-one $9\times9$ matrix $X_t = bc^T$ contributes to all blocks $(k,i)$ where $b$ has nonzero B-block $k$ components AND $c$ has nonzero C-block $i$ components. If $X_t$ contributes to $m$ core blocks, it saves $m-1$ terms. Need $\sum_t (m_t - 1) \ge 5$.

Example sharing patterns that save 5:
- 5 terms each shared between 2 blocks
- 2 terms shared between 3 blocks + 1 shared between 2
- 1 term shared between 3 + 1 between 4 (or similar)

## 12. Open Mathematical Questions

### For the upper bound (rank ≤ 22):
**Q1.** Does $R_{\mathbb F_2}(T_{\rm core}) \le 19$? Equivalently, can 19 rank-one $9\times9$ matrices over $\mathbb F_2$ cover all 8 core slices?

### For the lower bound (rank ≥ 21):
**Q2.** Does any set of 19 nonzero vectors $\bar a_1,\ldots,\bar a_{19} \in \mathbb F_2^8$ and rank-one matrices $X_1,\ldots,X_{19}$ satisfy the core equations
$$\sum_{t:\bar a_t(\alpha)=1}X_t=S_\alpha\quad\text{for all 8 core directions }\alpha?$$
A positive answer gives $R_{\mathbb F_2}(T)\le22$.

**Q2-lift.** Among such exact 19-term cores, can any choice of lift bits satisfy
$$\mathrm{rank}(M_0+\sum_{\varepsilon_t=1}X_t)\le1?$$
The non-existence of every exact core with this lift condition would exclude full rank 20 and prove $R_{\mathbb F_2}(T)\ge21$; excluding every 19-term core is a stronger sufficient route.

### Structural question:
**Q3.** Can the global rank-one residual constraint be shown to be incompatible with exact 19-term core decompositions, possibly by linking lift-bit block equations with tight contraction domains and the fact that no single rank-one perturbation reduces $I_3$ below rank 2?

---

## Files

- [core_tensor_analysis.py](../code/core_tensor_analysis.py): full tensor and core construction, flattening ranks, rank-23 analysis
- [core_block_analysis.py](../code/core_block_analysis.py): block sharing, $I_3$ decompositions, residual geometry, projected A analysis
- `workspace/data/core_analysis/`: saved tensors (.npy) and analysis results
