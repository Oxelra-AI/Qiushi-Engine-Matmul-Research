# Low-Excess Factor Geometry, Purity-Side 2-SAT, and Rank-19 Structural Obstructions

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

research: research_record.  Field: $\mathbb{F}_2$.  Object: E11 quotient core of $T_{\langle 3,3,3\rangle}$.

## 1. Sylvester Excess Bound (Theorem)

For a core slice $s$ with capacity $m$ (i.e., $m$ active rank-one terms) and block $(R_j, C_i)$:
$$B_s C_s^T = M_s \quad (\text{rank } 3)$$

where $B_s$ is the $9\times m$ matrix of active $b$-vectors and $C_s$ the $9\times m$ matrix of active $c$-vectors.

**Sylvester's rank inequality:** $\operatorname{rank}(B_s C_s^T) \ge \operatorname{rank}(B_s) + \operatorname{rank}(C_s) - m$.

Since $M_s$ has rank 3: $\operatorname{rank}(B_s) + \operatorname{rank}(C_s) \le m + 3$.

Since $\operatorname{col}(M_s) = R_j \subseteq \operatorname{span}(B_s)$ and $\operatorname{row}(M_s) = C_i \subseteq \operatorname{span}(C_s)$:
$\operatorname{rank}(B_s) \ge 3$ and $\operatorname{rank}(C_s) \ge 3$.

**Define excess:** $e_B = \operatorname{rank}(B_s) - 3$, $e_C = \operatorname{rank}(C_s) - 3$.  Both are $\ge 0$.

**Excess bound:**
$$\boxed{e_B + e_C \le m - 3}$$

### Consequences by capacity

| Capacity $m$ | Excess bound | Implication |
|:---:|:---:|:---|
| 3 | $e_B + e_C \le 0$ | Two-sided purity: all $b_t \in R_j$ and all $c_t \in C_i$ |
| 4 | $e_B + e_C \le 1$ | **One-sided purity:** at least one of $e_B, e_C$ equals 0 |
| 5 | $e_B + e_C \le 2$ | Bounded leakage: at most 2 excess dimensions total |

Capacity-3 two-sided purity was established in analysis (block-spread analysis).  Capacity-4 one-sided purity is new.

## 2. Pool Verification

Tested on all 519 rows of the rank-21 E11 core pool (verified decompositions with actual $B/C$ factors):

- **Sylvester bound:** verified on all 4,152 slice-row pairs.
- **Excess bound:** verified on all slice-row pairs.
- **Cap-4 one-sided purity:** all 260 cap-4 instances satisfy $e_B = 0$ or $e_C = 0$.
  - Breakdown: 128 with $(e_B, e_C) = (0,1)$ (B-pure), 132 with $(1,0)$ (C-pure).
- **Cap-5 excess:** 527 instances: 486 with $(1,1)$, 21 with $(0,2)$, 20 with $(2,0)$.

These match the independent peer verification (research_record record).

## 3. Global Purity-Side 2-SAT

The per-slice excess bounds extend to a **global consistency test** through the sharing structure.

### E11 core block structure

The 8 core slices have block positions $(j, i)$ where $j$ is the row group index and $i$ is the column group index:

| Slice $s$ | Block $(j, i)$ | Row group $R_j$ | Col group $C_i$ |
|:---:|:---:|:---:|:---:|
| 0 | (1, 0) | $R_1$ | $C_0$ |
| 1 | (2, 0) | $R_2$ | $C_0$ |
| 2 | (0, 1) | $R_0$ | $C_1$ |
| 3 | (1, 1) | $R_1$ | $C_1$ |
| 4 | (2, 1) | $R_2$ | $C_1$ |
| 5 | (0, 2) | $R_0$ | $C_2$ |
| 6 | (1, 2) | $R_1$ | $C_2$ |
| 7 | (2, 2) | $R_2$ | $C_2$ |

### Sharing incompatibility

If two slices $s_1, s_2$ share a term $t$ (i.e., the A-direction $a_t$ has both bits $s_1$ and $s_2$ set), then:
- **Different row groups** ($j_1 \ne j_2$): $b_t$ cannot simultaneously lie in both $R_{j_1}$ and $R_{j_2}$ (disjoint groups), so both slices cannot be B-pure.
- **Different col groups** ($i_1 \ne i_2$): similarly, both slices cannot be C-pure.

### 2-SAT formulation

For each slice $s$, define Boolean variables $B_s$ (B-pure) and $C_s$ (C-pure).

**Clauses:**
- **Cap-3 slices:** $B_s \wedge C_s$ (unit clauses — both sides forced pure).
- **Cap-4 slices:** $B_s \vee C_s$ (at least one side must be pure).
- **Sharing + different $j$:** $\neg B_{s_1} \vee \neg B_{s_2}$.
- **Sharing + different $i$:** $\neg C_{s_1} \vee \neg C_{s_2}$.

This is a **2-SAT** system on at most 16 variables (2 per slice).  UNSAT means the A-support is **provably incompatible** with any rank-one factorization of the core.

### Structural invariants

**Cross pairs:** 14 slice pairs with different $j$ AND different $i$:
$(0,2), (0,4), (0,5), (0,7), (1,2), (1,3), (1,5), (1,6), (2,6), (2,7), (3,5), (3,7), (4,5), (4,6)$.

**Latin triples:** 4 sets of 3 slices with pairwise different $j$ and $i$:
$(0,2,7), (0,4,5), (1,2,6), (1,3,5)$.

## 4. Novel A-Level Obstructions

### Cross-pair obstruction

> **If a cap-3 slice shares a term with a cap-4 slice and they form a cross pair (different $j$ AND different $i$), the 2-SAT is immediately UNSAT.**

*Proof:* Cap-3 forces $B_{s_1} = C_{s_1} = 1$.  Sharing + different $j$ gives $\neg B_{s_2}$.  Sharing + different $i$ gives $\neg C_{s_2}$.  But cap-4 requires $B_{s_2} \vee C_{s_2}$.  Contradiction.

### Latin triple obstruction

> **If three mutually-sharing cap-$\le 4$ slices form a Latin triple, the 2-SAT is UNSAT.**

*Proof:* All $j$'s differ: at most one slice can be B-pure ($\le 1$ B-pure). All $i$'s differ: at most one can be C-pure ($\le 1$ C-pure).  So at most 2 of 3 slices have a pure side, but cap-$\le 4$ requires all 3 to have one.

### Universality for 5 cap-3 + 3 cap-4

> **All 56 configurations of 5 cap-3 slices among 8 have at least 5 cap3-cap4 cross pairs.**

Distribution: 4 configs with 5 cross pairs, 12 with 6, 12 with 7, 12 with 8, 12 with 9, 4 with 10.

For a rank-19 support with the minimum capacity profile (5 cap-3 + 3 cap-4, total weight 27): a single shared direction hitting any of the $\ge 5$ cross pairs makes the support impossible.

### Latin triple trigger directions

Each Latin triple can be triggered by any direction with all three bits set.  Per triple, 32 of 255 nonzero directions are trigger directions.  The 4 triples cover different bit patterns, so a substantial fraction of high-weight directions are triggers for at least one triple.

## 5. Empirical Filter Power for Rank-19

### Weight-30 supports (8 weight-1 + 11 weight-2 directions)

- 11,055 valid supports found (all caps $\ge 3$) from 50,000 random samples
- **99.4% UNSAT** (only 65 pass the 2-SAT)
- Cap-3/4 distribution: 5 cap-3/4 (254), 6 (4,446), 7 (5,679), 8 (676)

### Weight ≤ 2 directions only (weight 30–38)

- 5,000 supports tested
- **75.2% UNSAT** overall
- By cap-3/4 count: 38% UNSAT at 3, 62.6% at 4, 79.1% at 5, 85.1% at 6, 91.9% at 7, 100% at 8

### Targeted low weight (weight 27–40)

| Weight | Tested | UNSAT | UNSAT % |
|:---:|:---:|:---:|:---:|
| 32 | 6 | 6 | 100% |
| 33 | 28 | 27 | 96.4% |
| 34 | 153 | 122 | 79.7% |
| 35 | 627 | 464 | 74.0% |
| 36 | 1,463 | 977 | 66.8% |
| 37 | 2,476 | 1,410 | 56.9% |
| 38 | 2,843 | 1,311 | 46.1% |
| 39 | 1,760 | 673 | 38.2% |
| 40 | 644 | 192 | 29.8% |

**The 2-SAT filter is most powerful exactly where rank-19 supports must live.**

## 6. Integration with Existing Machinery

The 2-SAT purity filter is **independent** of:
- Wang occupation (based on restriction-subspace bounds)
- Shadow/trace certificates (based on dual-basis equations)
- Block-spread R1/R2 constraints (based on block hit counts)

It is **complementary**: each layer reduces the search space by a different mechanism.  A practical rank-19 construction pipeline would apply:

1. Wang occupation feasibility (417,199 rows)
2. **Purity-side 2-SAT** (instant, eliminates 50–99% at low weight)
3. Shadow trace consistency (guarded, 171 variables per support)
4. Block-spread R1/R2 (block-hit necessary conditions)
5. GL$_3(\mathbb{F}_2)$ cap-3 completion (168 choices per cap-3 slice)
6. Rank-one $B/C$ factor completion (648 Brent equations)

Each surviving support at analysis comes with forced purity assignments that constrain the subsequent $B/C$ search.

## 7. Cap-5 Extension: Cross-Group Forced Purity

The 2-SAT can be strengthened by propagating purity through cap-5 slices.

**Theorem (Cap-5 Forced Purity):** If a cap-5 slice $s$ shares terms with cap-3 slices from *both* non-own row groups (i.e., cap-3 slices with row groups $j_1 \ne j_s$ and $j_2 \ne j_s$, $j_1 \ne j_2$), then $e_B \ge 2$, forcing $e_C = 0$ (C-pure). Similarly for column groups.

*Proof:* Each shared term $t_k$ has $b_{t_k} \in R_{j_k}$ (from cap-3 B-purity). The outside-block projections of $b_{t_1}$ and $b_{t_2}$ relative to $R_{j_s}$ lie in $R_{j_1}$ and $R_{j_2}$ respectively. Since $R_{j_1} \cap R_{j_2} = \{0\}$ (disjoint row groups), these projections are linearly independent, giving $e_B \ge 2$. With $e_B + e_C \le 2$: $e_C = 0$.

### Empirical improvement

| Test regime | Base 2-SAT survivors | Extended survivors | Extension kills | Improvement |
|:---|:---:|:---:|:---:|:---:|
| Weight 30 | 43 / 10,943 | **5 / 10,943** | 38 | 88.4% of survivors |
| Weight 27–40 | 1,898 / 3,865 | 1,690 / 3,865 | 208 | 11.0% of survivors |

At weight 30, the combined filter achieves **99.95% UNSAT** — only 5 out of 10,943 valid supports survive.

## 8. review-Verified Weighted Leakage Inequality (Strengthening)

review verification confirms the framework and derives a stronger generalization.

**Weighted leakage per cap-3 sharing:** For cap-3 slice $u$ sharing $h_{su}$ terms with slice $s$:
$$h_{su}\bigl(\mathbf{1}[j_s \ne j_u] + \mathbf{1}[i_s \ne i_u]\bigr) \le m_s - 3.$$

**Aggregated lower bounds:** Define
$$\ell_B(s) = \sum_{k \ne j_s} \max_{u: m_u=3,\, j_u=k} |I_s \cap I_u|, \qquad
\ell_C(s) = \sum_{\ell \ne i_s} \max_{u: m_u=3,\, i_u=\ell} |I_s \cap I_u|.$$

Then $e_B(s) \ge \ell_B(s)$ and $e_C(s) \ge \ell_C(s)$, giving:
$$\boxed{\ell_B(s) + \ell_C(s) \le m_s - 3.}$$

**Immediate consequences:**
- Cap-4 + cross-pair cap-3 sharing $h \ge 1$ items → $h \cdot 2 \le 1$, impossible for $h \ge 1$. (Recovers cross-pair obstruction.)
- Cap-5 + cross-pair cap-3 sharing 1 item → $(e_B, e_C) \ge (1, 1)$, neither side pure, excess budget exactly saturated.
- Cap-5 + two non-own row groups sharing + one is cross-pair → $e_B + e_C \ge 3 > 2$, **direct UNSAT**.

The weighted leakage and the 2-SAT are **complementary**: at weight 30, the extended 2-SAT leaves 5 survivors while the weighted leakage leaves 27 (from different obstructions). Combined, the filter is even stronger.

### Three-tier filter comparison (empirical)

| Weight regime | Base 2-SAT | Extended 2-SAT | Weighted leakage |
|:---|:---:|:---:|:---:|
| Weight 30 (10,943 valid) | 43 survive (0.39%) | **5 survive (0.05%)** | 27 survive (0.25%) |
| Weight 27–40 (3,865 valid) | 1,898 (49.1%) | 1,690 (43.7%) | **1,381 (35.7%)** |

## 9. Artifacts

- [excess_geometry_2sat.py](../code/excess_geometry_2sat.py): main framework
- [rank19_2sat_test.py](../code/rank19_2sat_test.py): uniform random test
- [lowweight_2sat_test.py](../code/lowweight_2sat_test.py): targeted low-weight test
- [excess_geometry_2sat.json](../results/excess_geometry/excess_geometry_2sat.json): full results
- [rank19_2sat_filter_test.json](../results/excess_geometry/rank19_2sat_filter_test.json): random test
- [rank19_lowweight_2sat_test.json](../results/excess_geometry/rank19_lowweight_2sat_test.json): low-weight test
- [extended_2sat.py](../code/extended_2sat.py): cap-5 extension comparison
- [extended_2sat_analysis.json](../results/excess_geometry/extended_2sat_analysis.json): extension results
