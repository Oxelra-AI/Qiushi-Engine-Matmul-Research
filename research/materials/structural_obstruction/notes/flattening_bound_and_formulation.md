# Factor-rank-sum flattening bound and proof architecture restructuring

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## 1. Flattening rank-sum bound (self-contained, field-independent)

### Statement

For any exact decomposition $T_{\langle 3,3,3 \rangle} = \sum_{t=1}^n a_t \otimes b_t \otimes c_t$ over any field $\mathbb{F}$,

$$\sum_{t=1}^n \operatorname{rank}(a_t) \ge 27,$$

where $\operatorname{rank}(a_t)$ is the matrix rank of $a_t$ viewed as a $3 \times 3$ matrix. The same holds with $b_t$ or $c_t$ in place of $a_t$.

### Proof

In the convention $T[3i+j, 3j+k, 3i+k] = 1$, split the A-slot into row/column indices:
$E_{ij} = e_i \otimes e_j$, giving a 4-way tensor
$$T = \sum_{i,j,k} e_i \otimes e_j \otimes E_{jk} \otimes E_{ik}$$
in $\mathbb{F}^3 \otimes \mathbb{F}^3 \otimes \mathbb{F}^9 \otimes \mathbb{F}^9$.

Flatten rows $(i, (j,k))$ against columns $(j, (i,k))$ to get a $27 \times 27$ matrix. The entry at row $(i, 3j+k)$, column $(j, 3i+k)$ is 1 (from the single nonzero $T[3i+j, 3j+k, 3i+k]$). Since the map $(i,j,k) \to (i \cdot 9 + 3j+k, \; j \cdot 9 + 3i+k)$ is a bijection on $\{0,\ldots,26\}^2$, this flattening is a **permutation matrix of rank 27**.

For a single decomposition term $a \otimes b \otimes c$ with $a = \sum_{i,j} a_{ij} e_i \otimes e_j$, the same flattening gives:
$$\Phi_A(a \otimes b \otimes c)[(i,\beta), (j,\gamma)] = a_{ij} \cdot b_\beta \cdot c_\gamma = (a \otimes b c^T)_{(i,\beta),(j,\gamma)},$$
which is the Kronecker product of $a$ (a $3 \times 3$ matrix of rank $r$) with $b c^T$ (a $9 \times 9$ matrix of rank 1). So $\operatorname{rank}(\Phi_A(\text{term}_t)) = \operatorname{rank}(a_t) \cdot 1 = \operatorname{rank}(a_t)$.

By rank subadditivity:
$$27 = \operatorname{rank}(\Phi_A(T)) \le \sum_{t=1}^n \operatorname{rank}(\Phi_A(\text{term}_t)) = \sum_{t=1}^n \operatorname{rank}(a_t). \qquad\square$$

### Verification

- Computationally verified: $\Phi_A(T_{333})$ is a $27 \times 27$ permutation matrix over $\mathbb{F}_2$ with rank 27.
- Generalized: $\Phi_A(T_{\langle n,n,n \rangle})$ has rank $n^3$ for $n = 2, 3, 4$.
- Positive controls:
  - flipcpd rank-23 text scheme: $\sum \operatorname{rank}(a_t) = 30 \ge 27$ ✓ (16 rank-1, 7 rank-2)
  - research_record validation scheme: $\sum \operatorname{rank}(a_t) = 32 \ge 27$ ✓ (14 rank-1, 9 rank-2)
  - research_record scheme: $\sum \operatorname{rank}(b_t) = 27$ (tight!) ✓

## 2. Consequence: E11 retired from the lower-bound proof

For a hypothetical rank-20 decomposition: $\sum \operatorname{rank}(a_t) \ge 27$ but $n = 20$, so the excess is $27 - 20 = 7$. Since each rank-2 factor adds 1 excess and each rank-3 adds 2:
- At least $\lceil 7/2 \rceil = 4$ A-factors have matrix rank $\ge 2$.
- Therefore a rank-2 or rank-3 pivot always exists; it is impossible for all A-factors to be rank 1.

**This means the lower-bound proof no longer requires closing the E11/rank-1 quotient.** To prove $R_{\mathbb{F}_2}(T_{\langle 3,3,3 \rangle}) \ge 21$, it suffices to show:

1. The rank-2 quotient $T/\langle p_{17} \rangle$ has no length-19 decomposition.
2. The rank-3 quotient $T/\langle p_{273} \rangle$ has no length-19 decomposition.

**What this retires:**
- The unreplayed earlier research rank-2 DRAT bridge
- The E11-specific rank-1 A-factor reduction argument
- The E11 residual-cap multiset problem (six repeatable directions)
- Any dependence on E11 for the lower-bound direction

**What this preserves:**
- E11 remains the BEST constructive surface (hill-climb reached 8 violations at n=19 vs 50 and 93 for rank-2 and rank-3)
- Both rank-2 and rank-3 have all 255 quotient lines at cap 1 for n=19, so distinct enumeration is complete
- Any rank-19 quotient decomposition for ANY pivot lifts to a full rank-$\le 22$ algorithm

## 3. Quotient B-slot flattening bounds

Applying the same flattening to the B-slot of each quotient tensor $Q_p$ (shape $8 \times 9 \times 9$):
$$\operatorname{rank}(\Phi_B(Q_p)) = 24 \quad \text{for all three pivots } p \in \{1, 17, 273\}.$$

Therefore, for any rank-$r$ decomposition of $Q_p$:
$$\sum_{t=1}^r \operatorname{rank}(b_t) \ge 24.$$

At $r = 19$: at least $\lceil(24-19)/2\rceil = 3$ B-factors have matrix rank $\ge 2$.

This is a **LUT-free constraint** that can be added to quotient_core_sat.py and fixed-A completion encodings.

Note: $\Phi_C(Q_p) = 3$ for all pivots, so the C-slot flattening is weak.

## 4. LUT audit via classical matmul ranks

The Wang LUT values are **quotient-rank** bounds: for a $d$-dimensional subspace $U$, $\text{LB}(U) = $ lower bound on $R(T/U)$, where $T/U$ is the $(9-d) \times 9 \times 9$ quotient tensor.

### Column-space subspaces
For $U_x = \{A : \operatorname{col}(A) \subseteq \operatorname{span}(x)\}$ ($\dim = 3$):
- $T/U_x \cong T_{\langle 2,3,3 \rangle}$ (the tensor for $2 \times 3$ by $3 \times 3$ multiplication)
- LUT value: $\text{LB} = 15$ for all three coordinate choices $x = e_0, e_1, e_2$
- This equals the known $R(T_{\langle 2,3,3 \rangle}) = 15$ (Hopcroft-Kerr, tight)
- **The LUT is consistent with classical algebraic complexity for these subspaces**

For $V_{x,y} = \{A : \operatorname{col}(A) \subseteq \operatorname{span}(x,y)\}$ ($\dim = 6$):
- $T/V_{x,y} \cong T_{\langle 1,3,3 \rangle}$ (row-vector times matrix)
- LUT value: $\text{LB} = 9$ for all sampled entries (200 dim-6 rows checked)
- This equals $R(T_{\langle 1,3,3 \rangle}) = 9$ (trivial, tight)
- **Consistent**

### Overall dim-3 distribution
From all 788,035 dim-3 subspaces of $\mathbb{F}_2^9$:
- LB = 15: 14 subspaces (the 6 column-space + 6 row-space + 2 diagonal types)
- LB = 16: 7,497 subspaces
- LB = 17: 378,182 subspaces  
- LB = 18: 402,342 subspaces

The minimum LB = 15 subspaces correspond exactly to column/row-space types with known quotient $T_{\langle 2,3,3 \rangle}$. All others have tighter bounds, consistent with their quotient tensors being more constrained than the rectangular matmul tensor.

## 5. New proof architecture

```
R_F2(T_{333}) >= 21:
  Flattening bound: sum rank(a_t) >= 27
    => at n=20, some a_t has rank >= 2
    => pick pivot p of rank 2 or 3

  Case rank(p) = 2 (pivot 17):
    Quotient T/span(p) is 8x9x9 with nnz 27, slices [6,3,3,3,3,3,3,3]
    All 255 quotient lines have cap 1 at n=19 (distinct enum complete)
    Need: no length-19 distinct decomposition exists  [OPEN]

  Case rank(p) = 3 (pivot 273):
    Quotient T/span(p) is 8x9x9 with nnz 30, slices [6,3,3,3,6,3,3,3]
    All 255 quotient lines have cap 1 at n=19 (distinct enum complete)
    Need: no length-19 distinct decomposition exists  [OPEN]

E11 (rank-1 quotient): NOT needed for lower bound, but best constructive surface.
```

## 6. Constructive pipeline

E11 is now purely upside for construction. The hill-climber reached 8 violations at n=19, suggesting the E11 occupation system at 19 is genuinely close to feasible. 

Pipeline:
1. Seed from known rank-21 supports by C(21,2)=210 deletions per row
2. Evaluate against complete E11 Wang system
3. Hill-climb from best seeds with plateau moves and large-neighborhood swap
4. Pipe zero-violation supports to fixed-A Brent completion (~1s per support)

Any rank-19 E11 decomposition lifts to rank-22 with no LUT trust needed.

## 7. Files produced

- [flattening_rank_sum_bounds.py](../../quotient_cores/code/flattening_rank_sum_bounds.py): verifies all flattenings and controls
- [flattening_rank_sum_bounds.json](../results/flattening_bounds/flattening_rank_sum_bounds.json): complete results
- [lut_dim3_dim6_audit.py](../../quotient_cores/code/lut_dim3_dim6_audit.py): LUT audit via classical ranks
- [lut_dim3_dim6_audit.json](../results/flattening_bounds/lut_dim3_dim6_audit.json): audit results
- [e11_deletion_seed_eval.py](../../quotient_cores/code/e11_deletion_seed_eval.py): constructive seed evaluation pipeline
