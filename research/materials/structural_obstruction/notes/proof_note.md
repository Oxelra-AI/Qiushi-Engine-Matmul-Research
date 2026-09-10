# Proof Note: R_{F_2}(T_{<3,3,3>}) ≥ 21

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Status: Conditional — needs certificate finalization

## Theorem Statement

Every bilinear algorithm for 3×3 matrix multiplication over F_2 requires at least 21 multiplications:
$$R_{\mathbb{F}_2}(T_{\langle 3,3,3\rangle}) \geq 21.$$

## Proof Architecture

The proof proceeds by contradiction. Assume a rank-20 decomposition
$$T = \sum_{t=1}^{20} A_t \otimes B_t \otimes C_t$$
exists, where $A_t, B_t, C_t \in \mathbb{F}_2^{3 \times 3}$ are nonzero.

### A-slot split flattening forces high-rank A-factors

The A-split flattening $\Phi_A(T)$ is a $27 \times 27$ permutation matrix $P$ of rank 27.
Under our convention $T[3i+j, 3j+k, 3i+k] = 1$:
$$P[(i,b),(j,c)] = \delta_{b=3j+k,\, c=3i+k \text{ for some } k}.$$
The flattening terms $M_t$ have $\operatorname{rank}(M_t) = \operatorname{rank}(A_t)$ since
$M_t = A_t \otimes \operatorname{vec}(B_t)\operatorname{vec}(C_t)^T$.

By rank subadditivity: $27 = \operatorname{rank}(P) \leq \sum_t \operatorname{rank}(A_t)$.
With 20 terms: $\sum_t (\operatorname{rank}(A_t) - 1) \geq 7$, so at least 4 terms have $\operatorname{rank}(A_t) \geq 2$.

**Verified**: P is a 27×27 permutation matrix; B and C slots also give rank-27 permutation flattenings by cyclic symmetry. [analysis, 22-23]

### All A-directions are distinct (Wang dim-1 values = 19)

Wang's certified lower bound 20 implies that for every 1-dimensional A-subspace $\langle p \rangle$, the quotient $T/\langle p \rangle$ has rank $\geq 19$ (the Wang LUT value for every dim-1 subspace).

In a rank-20 decomposition, if $A_s = A_t$ for some $s \neq t$, then quotienting by $\langle A_t \rangle$ removes both terms, leaving $\leq 18$ terms for a tensor of rank $\geq 19$. Contradiction.

Therefore all 20 A-factors are distinct as matrices: $A_s \neq A_t$ for $s \neq t$.

**Verified**: All 511 dim-1 LUT values equal 19. [earlier analysis, 14]

### High-rank pairs force rank-one differences (dim-2 raises)

Consider two high-rank ($\geq 2$) factors $A_s, A_t$ with $s \neq t$. Their span $W = \langle A_s, A_t \rangle$ is a 2-dimensional A-subspace with three nonzero elements: $A_s, A_t, A_s + A_t$.

Under the $\operatorname{GL}_3 \times \operatorname{GL}_3$ action, dim-2 subspaces fall into 14 orbits (indices 478-491 in Wang's certificate).

**Key observation**: The only orbits whose three nonzero elements are ALL of rank $\geq 2$ are orbits 484-491. All other orbits with two high-rank elements necessarily have $A_s + A_t$ of rank 1, which makes the pair "coset-compatible."

- Orbits with rank patterns including rank-1: 478=(1,1,1), 479=(1,2,2), 480=(1,1,2), 481=(1,2,2), 482=(1,3,3), 483=(1,2,3).
- All-high-rank orbits: 484=(2,2,2), 485=(2,2,2), 486=(2,2,2), 487=(2,3,3), 488=(2,2,3), 489=(2,2,2), 490=(2,3,3), 491=(3,3,3).

**Dim-2 occupation raises**: For each of orbits 484-491, the Wang LUT value is 18. We prove it should be raised to 19: the integer occupation system at target length 18, using all inherited Wang rows from strict super-subspaces, is infeasible. This was verified by:
- CP-SAT with integer multiplicity variables (NewIntVar(0, L)): INFEASIBLE for all 8 orbits
- Independent SciPy/HiGHS MILP: integer-INFEASIBLE for all 8 orbits

**Critical note on orbit 489**: This orbit has one dim-3 superspace with LUT value 16, giving a line cap of 2 (not 1). The integer multiplicity model correctly handles this. A distinct-support DFS would NOT be valid for orbit 489. All other 7 orbits have max line cap = 1.

Therefore, quotienting by any all-high-rank dim-2 span removes at least 2 terms from the decomposition but the quotient tensor has rank $\geq 19$, leaving $\leq 18$ terms. Contradiction. So no high-rank pair can span an all-high-rank dim-2 subspace, meaning $A_s + A_t$ must have rank 1 for every pair of high-rank factors.

### Common coset reduction

We have $\geq 4$ high-rank factors with pairwise rank-one differences. Over $\mathbb{F}_2$:

**Lemma**: If $\{A_1, \ldots, A_h\}$ are distinct matrices in $\mathbb{F}_2^{3 \times 3}$ with $h \geq 3$ and $\operatorname{rank}(A_i + A_j) = 1$ for all $i \neq j$, then there exist $u, v \in \mathbb{F}_2^3$ such that all $A_i$ lie in the affine coset $A_1 + uv^T \cdot \mathbb{F}_2$ or $A_1 + \mathbb{F}_2 \cdot u'v'^T$.

More precisely: $A_i + A_j = u_{ij} v_{ij}^T$ with rank 1. For three distinct indices $i,j,k$:
$(A_i + A_j) + (A_j + A_k) = A_i + A_k$, so $u_{ij}v_{ij}^T + u_{jk}v_{jk}^T$ has rank 1.
Over $\mathbb{F}_2$, a sum of two rank-1 matrices having rank 1 forces them to share a common left vector or a common right vector. Iterating this through all triples forces all differences into one of two patterns:
- Column type: $A_i - A_1 = u \cdot w_i^T$ for a fixed $u$ (common left vector)
- Row type: $A_i - A_1 = w_i \cdot v^T$ for a fixed $v$ (common right vector)

Under $\operatorname{GL}_3 \times \operatorname{GL}_3$ invariance, normalize to $u = e_1$ (column type) or $v = e_1^T$ (row type).

### AG(3,2) cap theorem collapses the residual

**Column type (normalized $u = e_1$):** The high-rank factors lie in $p + e_1 \otimes \mathbb{F}_2^3$ where the lower-block matrix $B$ has rank 2 (rank-1 lower block gives at most 6 rank-2 elements, insufficient for the excess $\geq 7$ requirement).

The coset $S = \langle p, e_1 \otimes e_1, e_1 \otimes e_2, e_1 \otimes e_3 \rangle$ is a dim-4 A-subspace with 15 nonzero elements. The first-row coordinate gives a map from $S$ to $\mathbb{F}_2^3$, identifying the 8 coset elements $\{p + e_1 w^T : w \in \mathbb{F}_2^3\}$ with the 8 points of $\mathbb{F}_2^3$. In the rank-2 lower-block case:
- 4 rank-2 coset elements (first-row labels with bit 0 = 0): labels $\{0,2,4,6\}$
- 4 rank-3 coset elements (first-row labels with bit 0 = 1): labels $\{1,3,5,7\}$

The dim-4 span $S$ has exactly 15 dim-3 subspaces. One is $R = \langle e_1 e_1^T, e_1 e_2^T, e_1 e_3^T \rangle$ (the rank-1 family) with $\operatorname{LB}(R) = 15$ (representing $T_{\langle 2,3,3\rangle}$). The remaining 14 dim-3 subspaces each contain 4 coset elements and 3 rank-1 elements, and correspond exactly to the 14 two-dimensional affine subspaces (4-element planes) of $\mathbb{F}_2^3$.

**Wang dim-3 table**: All 651 coset-derived dim-3 subspaces across all 63 cosets have LUT value exactly 17. For the normalized coset, all 14 non-$R$ dim-3 subspaces have $\operatorname{LB} = 17$, giving cap $= 20 - 17 = 3$.

**AG(3,2) cap theorem (verified computationally)**: $\mathbb{F}_2^3$ has exactly 14 four-element affine planes. The cap number of $\operatorname{AG}(3,2)$ is 4: every 5-element subset of $\mathbb{F}_2^3$ contains a 4-element plane.

Since each plane's dim-3 subspace has $\operatorname{LB} = 17$ and cap $= 3$, the total number of A-factors in any plane is $\leq 3$. A 4-element plane that is entirely contained in $H$ would have $|H \cap \text{plane}| = 4 > 3$. Therefore $H$ contains no complete plane, giving $|H| \leq 4$.

Combined with the flattening lower bound $|H| \geq 4$: exactly $|H| = 4$.

The four rank-3 labels $\{1,3,5,7\}$ form a 4-element plane, so $|H \cap \{1,3,5,7\}| \leq 3$. The flattening forces $16 + 2|H_2| + 3|H_3| \geq 27$ with $|H_2| + |H_3| = 4$, giving $|H_3| \geq 3$. Combined: exactly $|H_3| = 3$ and $|H_2| = 1$.

Total A-rank sum: $16 \cdot 1 + 1 \cdot 2 + 3 \cdot 3 = 27 = \operatorname{rank}(P)$. **Zero excess**.

**Row type**: Under this investigation's convention $T[3i+j, 3j+k, 3i+k] = 1$ (i.e., $f(X,Y,Z) = \operatorname{tr}(XYZ^T)$), the correct A-transposing automorphism is $(A,B,C) \mapsto (A^T, C, B)$ (NOT $(A^T, C^T, B^T)$). This was verified on 200,000 random triples with zero failures and by checking $T = T'$ under the permuted tensor.

The LUT is transpose-invariant: $\operatorname{LB}(W) = \operatorname{LB}(W^T)$ for all 8,283,458 subspaces, with zero mismatches. So the row-type coset analysis follows by symmetry.

### Saturated product identity — final contradiction

**Saturation Lemma** (field-independent): If $P$ is invertible, $P = \sum_{t=1}^r M_t$, and $\sum_t \operatorname{rank}(M_t) = \operatorname{rank}(P)$, then:
$$M_t P^{-1} M_s = \delta_{ts} M_t \quad \text{for all } t, s.$$

*Proof*: The column spaces $\operatorname{col}(M_t)$ form a direct-sum decomposition of $\mathbb{F}^n$ (by rank subadditivity equality). The projections $E_t = P^{-1} M_t$ are orthogonal idempotents: $E_t E_s = \delta_{ts} E_t$, $\sum_t E_t = I$. Multiplying by $P$: $M_t P^{-1} M_s = P E_t E_s = \delta_{ts} M_t$.

**Product Identity** (verified on 50,000 random triples):
$$M(A_t,B_t,C_t) P^{-1} M(A_s,B_s,C_s) = M(A_t B_s C_t^T A_s, B_t, C_s).$$

**Diagonal case** ($t = s$, invertible $A_t$):
$M_t P^{-1} M_t = M_t$ gives $A_t B_t C_t^T A_t = A_t$, hence $B_t C_t^T = A_t^{-1}$.
Therefore $B_t$ and $C_t$ are invertible.

**Off-diagonal case** ($t \neq s$, both $A_t, A_s$ invertible):
$M_t P^{-1} M_s = 0$ gives $A_t B_s C_t^T A_s = 0$.
But $A_t, A_s$ are invertible (given), and $B_s, C_t$ are invertible (from the diagonal case for $s$ and $t$ respectively).
A product of four invertible matrices has rank 3 $\neq 0$. **Contradiction**.

Therefore: a zero-excess decomposition can have **at most one** invertible A-factor.
The forced profile requires three rank-3 (invertible) A-factors. **QED**.

## Computational Premises

The proof uses the following verified computational facts:

1. **Wang lower bound 20**: Independently replayed certificate, SHA256 `25595a883ce877eecd802139ff4e07646e154b2797ad6fe7f9ec737ab0c6135d`. [analysis]

2. **All dim-1 LUT values = 19**: Verified across all 511 one-dimensional subspaces. [earlier analysis, 14]

3. **Eight dim-2 occupation raises** (orbits 484-491 from LB=18 to LB=19):
   - CP-SAT INFEASIBLE with integer multiplicity variables: all 8 orbits
   - Independent SciPy/HiGHS MILP: integer-INFEASIBLE for all 8 orbits
   - Orbit 489 has one direction with line cap = 2; integer model is essential

4. **651 coset dim-3 LUT values = 17**: Exact lookup from the certified LUT for all dim-3 subspaces arising from normalized column-type cosets. [earlier analysis]

5. **LUT transpose invariance**: LB(W) = LB(W^T) for all 8,283,458 subspaces, zero mismatches. [analysis]

6. **Transpose automorphism**: (A,B,C) → (A^T, C, B) under convention T[3i+j,3j+k,3i+k]=1. Verified on 200,000 random triples with zero failures; tensor symmetric under this map. The WRONG automorphism (A^T, C^T, B^T) fails on 97,025/200,000 triples. [analysis]

7. **Split flattening**: A-slot flattening of T_{<3,3,3>} is a 27×27 permutation matrix. [earlier analysis, 22-23]

8. **Product identity**: M(A_t,B_t,C_t) P^{-1} M(A_s,B_s,C_s) = M(A_t B_s C_t^T A_s, B_t, C_s). Verified on 50,000 random triples with zero failures. Off-diagonal rank always 3 for invertible inputs (10,000 samples). [earlier analysis]

9. **GL3×GL3 invariance**: GL_3(F_2) is transitive on F_2^3 \ {0} (reaching all 7 nonzero vectors from e_1). LUT values invariant under the GL_3×GL_3 action (1,400 sampled transforms, zero failures). [analysis]

10. **Coset lemma**: Exhaustively verified for h=3 (49,882 triples, all in column or row coset) and h=4 (24,778 quads, all in column or row coset). Zero counterexamples. [analysis]

11. **AG(3,2) cap theorem**: F_2^3 has exactly 14 four-element affine planes. Cap number = 4: every 5-subset contains a plane. Verified by exhaustive enumeration. [analysis]

## Remaining Proof Obligations

- [ ] Proof-logging certificates for the 8 dim-2 raises (PB format or proof-logging MILP)
- [ ] Clean written proof of the coset lemma (rank-one-difference implies common row/column)  
- [ ] AG(3,2) plane-counting derivation (every 5-subset contains a plane)
- [ ] Formal saturation lemma proof (currently verified numerically, algebraic proof is elementary)
- [ ] Row-to-node mapping for LUT values used in the proof
- [ ] Independent reproduction by peer research research_record

## Corroborating Evidence (not part of the proof)

- 16 normalized column-type H configurations: all CP-SAT INFEASIBLE + HiGHS integer-INFEASIBLE [analysis]
- 16 row-type transposed configurations: all CP-SAT INFEASIBLE [analysis]
- H00 safe-DFS complete enumeration: zero solutions at target 16 from 43-point domain [analysis]
- H00 ladder: feasible at lengths 21-24, confirming the model is at its exact edge [analysis]
- Order-96 stabilizer transitive on 16 column configurations [analysis]
