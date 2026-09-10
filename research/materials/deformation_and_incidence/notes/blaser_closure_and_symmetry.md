# Bläser closure via Conner–Harper–Landsberg, border rank theorem, and symmetry-invariant analysis

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

**analysis correction.** Section 3.1 below used an imprecise sandwich action formula. The preserving finite QMM convention for a diagonal sandwich \(\phi_{F,F,F}\) is recorded and checked in [order7_certificate_and_order3_setup.md](../../symmetry_and_residuals/notes/order7_certificate_and_order3_setup.md): on UV covectors, row-major \(X\mapsto F^T X F^{-T}\), and on W-slice coefficients \(X\mapsto F^{-1}XF\), with exact check `gE*T_flat = T_flat*hW`. The analysis random order-7 orbit search is superseded by the analysis replayable certificate in [order7_family_certificate_v2.json](../../symmetry_and_residuals/results/order7_exhaustive/order7_family_certificate_v2.json).

## 1. Bläser dependency closed (major result)

The aligned-stratum exclusion (earlier analysis) required $R(M_{\langle 3,3,2 \rangle}) \geq 14$ as its sole zero-margin external input. This is now established through the following chain, requiring no further primary-source search:

**ARTIFACT A.** Conner, Harper, and Landsberg (2023) prove
$$\underline{R}(M_{\langle 2,3,3 \rangle}) = 14$$
in *Forum of Mathematics, Pi*, DOI `10.1017/fmp.2023.14` (\cite{conner2023lowera}). This is the exact border rank: both $\underline{R} \geq 14$ and $\underline{R} \leq 14$ are established.

**ARTIFACT B.** Tensor rank and border rank are invariant under cyclic permutation of factors:
$$R(M_{\langle a,b,c \rangle}) = R(M_{\langle b,c,a \rangle}), \qquad \underline{R}(M_{\langle a,b,c \rangle}) = \underline{R}(M_{\langle b,c,a \rangle}).$$
Applied to $(a,b,c) = (2,3,3)$: $(2,3,3) \to (3,3,2)$ is a cyclic permutation, so
$$\underline{R}(M_{\langle 3,3,2 \rangle}) = \underline{R}(M_{\langle 2,3,3 \rangle}) = 14.$$

**ARTIFACT C.** Rank is at least border rank: $R(T) \geq \underline{R}(T)$ for any tensor. Therefore
$$R(M_{\langle 3,3,2 \rangle}) \geq 14.$$

This closes the Bläser dependency. The aligned-stratum exclusion is now:

**Theorem.** Over any characteristic-zero field $K$, no full-span rank-22 decomposition of $T_{\langle 3,3,3 \rangle}$ admits a noncentral Lie-algebra stabilizer element acting projectively termwise on the summands.

*Proof.* The nonsemisimple lemma (analysis) forces such stabilizer elements to be semisimple. The exact rational enumeration (analysis) finds 6,424 noncentral repeated-difference weight flats. Their certified block-rank sums are $\{23:36, 24:108, 25:27, 27:6253\}$. The block-rank inputs are:
- $R(M_{\langle 3,3,2 \rangle}) \geq 14$ (Steps A–C above)
- $R(M_{\langle 3,2,2 \rangle}) \geq 8$ (exterior flattening, self-contained)
- $R(M_{\langle 2,2,2 \rangle}) \geq 6$ (Strassen/exterior flattening)

All 6,424 sums are $\geq 23 > 22$, excluding every noncentral aligned pattern.

**Detail on the 36 critical flats (sum = 23).** review verification clarified that these split into:
- 9 flats with block structure containing $M_{\langle 3,3,2 \rangle}$ at the critical bound: sum $14 + 9 = 23$. These depend on $R(M_{\langle 3,3,2 \rangle}) \geq 14$.
- 27 flats whose critical block is $M_{\langle 3,2,2 \rangle}$: with the internal bound $\geq 8$, their sums are 23; with CHL's improved bound $R(M_{\langle 3,2,2 \rangle}) \geq 10$, these rise to $\geq 25$.

Thus the only truly zero-margin patterns are the 9 depending on the $\geq 14$ input.

**Scope.** This theorem applies to:
- Characteristic-zero fields (by $\mathbb{Q}$-subdomain $\hookrightarrow \mathbb{C}$ embedding).
- Lie-algebra stabilizer elements acting additively on the weight lattice. Finite-order group elements with multiplicative weight coincidences are not automatically covered by the additive enumeration.
- Positive characteristic is NOT covered by the CHL chain alone. □

**Bonus.** The same source also gives $\underline{R}(M_{\langle 2,2,3 \rangle}) = 10$, hence $R(M_{\langle 3,2,2 \rangle}) \geq 10$, strengthening our internal bound of 8. This does not change the aligned-stratum conclusion but makes the margin larger.

## 2. Border rank of $T_{\langle 3,3,3 \rangle}$ and structural degeneration

**Theorem.** $17 \leq \underline{R}(T_{\langle 3,3,3 \rangle}) \leq 20$.

Sources:
- Lower bound: Conner–Harper–Landsberg (2023), $\underline{R}(M_{\langle 3 \rangle}) \geq 17$ (\cite{conner2023lowera}).
- Upper bound: Smirnov (2013), referenced as [29] in Landsberg–Michałek (2016, Remark 2.1): $\underline{R}(M_{\langle 3 \rangle}) \leq 20$ (\cite{landsberg2016geometry}).

**Consequence.** Since $\underline{R}(T_{333}) \leq 20 < 22$, the tensor $T_{333}$ lies in $\overline{\sigma_{20}} \subset \overline{\sigma_{22}}$ (Zariski closure). Therefore:
1. In the Zariski or Euclidean topology on $\mathbb{C}^{729}$, every neighborhood of $T_{333}$ contains rank-$\leq 20$ tensors.
2. If $R(T_{333}) > 22$, then $T_{333}$ is on the boundary of $\sigma_{22}$, not in its interior.
3. **Conditional degeneration theorem.** If $R(T_{333}) > 22$ and $T_{333} = \lim_{t \to 0} \sum_{i=1}^{22} s_i(t)$ with each $s_i(t)$ rank one, then the rank-one summands $s_i(t)$ cannot all remain bounded as $t \to 0$. At least one must diverge, producing the cancellation observed numerically.

The condition $R(T_{333}) > 22$ is crucial: the border rank bound alone does NOT exclude a bounded rank-22 decomposition. If $R(T_{333}) \leq 22$, a bounded decomposition could exist (but our numerical methods have not found one).

**Structural interpretation of numerical evidence.** Our earlier analysis and 24–26 degeneration observations are consistent with (and structurally explained by) the border rank bound. The residual approaching zero with diverging parameters is a necessary feature near any point of $\overline{\sigma_r} \setminus \sigma_r$. This does not prove $R(T_{333}) > 22$, but it shows that numerical continuation near known rank-23 seeds cannot distinguish the two cases.

**Research implication:** Exact algebraic or finite-field methods remain the primary routes for either finding a rank-22 decomposition or proving it doesn't exist. Numerical methods near known seeds provide diagnostic evidence but not proof.

## 3. Symmetry-invariant analysis over $\mathbb{F}_2$

### 3.1. Sandwich action on $E/L$

For a sandwich element $(F,F,F)$ with $F \in GL_3(\mathbb{F}_2)$, the action on $E = \mathbb{F}_2^{81}$ is $g = (F \otimes F^{-T})^{\otimes 2}$.

**Eigenspace decomposition on $E/L$ ($= \mathbb{F}_2^{72}$):**

| Element | Order | Fixed | Type 1 | Type 2 | Total |
|---------|-------|-------|--------|--------|-------|
| $F_7$ (Singer, order 7) | 7 | 12 | 30 ($x^3+x+1$) | 30 ($x^3+x^2+1$) | 72 |
| $F_3$ (cyclic perm, order 3) | 3 | 24 | 48 ($x^2+x+1$) | — | 72 |
| $T_2$ (transvection, order 2) | 2 | 36 | — | — | 72 |

**Joint fixed subspace under $\langle F_7, T_2 \rangle = GL_3(\mathbb{F}_2)$: dimension 1.**

This means the full sandwich group fixes exactly a 1-dimensional subspace of $E/L$.

### 3.2. L decomposition under each element

| Element | $\dim(\text{Fix} \cap L)$ |
|---------|--------------------------|
| $F_7$ | 3 |
| $T_2$ | 5 |
| $F_3$ | 3 |

### 3.3. Rank-one orbit structure

| Element | Fixed rank-one | Free orbits | Orbit size |
|---------|---------------|-------------|------------|
| $F_7$ | 49 | 37,296 | 7 |
| $F_3$ | 49 | 87,024 | 3 |

**Key structural fact:** All 49 fixed rank-one points:
- Span exactly 9 dimensions in $E$
- Have quotient rank 9 (span 9 dims in $E/L$)
- Have **zero** intersection with $L$

This means for any sandwich-invariant decomposition with a fixed summand, that summand contributes ZERO L-directions. All 9 dimensions of L must be covered by the free orbits.

### 3.4. Invariant 13-plane counts (too large for brute enumeration)

For single prime-order elements:
- Order-7: $\sim 1.85 \times 10^{33}$ invariant 13-planes
- Order-3: $\sim 3.46 \times 10^{68}$ invariant 13-planes

These are not enumerable. The full sandwich group (with joint fixed dim = 1) would give a much smaller count, but computing the full module decomposition requires the MeatAxe or equivalent.

### 3.5. Implications for the search

For a fully $GL_3(\mathbb{F}_2)$-sandwich-invariant rank-22 decomposition:
1. The UV span must be a 22-dim invariant subspace of $E$ containing $L$
2. The quotient must be a 13-dim invariant subspace of $E/L$ with 1 fixed direction
3. The remaining 12 dims must come from non-trivial $GL_3(\mathbb{F}_2)$-modules
4. Over $\mathbb{F}_2$, the simple modules of $GL_3(\mathbb{F}_2)$ have dimensions 1, 3, 3, 8
5. $12 = 4 \times 3$ is the only decomposition without the Steinberg (dim 8)
6. $12 = 8 + 3 + 1$... but 1 is trivial and we only have 1 copy. $12 = 8 + 4$, but 4 ≠ 3k. So only $12 = 4 \times 3$ works for semisimple modules.

**Conclusion:** A fully sandwich-invariant 13-plane in $E/L$ must contain the unique trivial direction plus 4 copies of the 3-dimensional simple modules ($V$ or $V^*$). The number of such subspaces depends on the multiplicities $a_1, a_2$ of $V$ and $V^*$ in $E/L$:
$$\text{count} = \sum_{b_1+b_2=4} \binom{a_1}{b_1}_2 \binom{a_2}{b_2}_2$$

This could be very manageable if $a_1, a_2$ are moderate.

### 3.6. Yang's exclusion gap

Yang (arXiv:2402.01011) excluded symmetric $\mathbb{F}_2$ decompositions of $T_{333}$ at rank $\leq 21$ under cyclic, cyclic+transpose, and cyclic+sandwich symmetries. **Rank 22 was deliberately omitted** because $\log_3 22 > \log_2 7$, making it asymptotically irrelevant.

This is precisely the gap our search addresses: sandwich-invariant rank-22 decompositions.

## 4. Files

- [symmetry_invariant_search.py](../../symmetry_and_residuals/code/symmetry_invariant_search.py): eigenspace and orbit computation
- [symmetry_eigenspace_analysis.json](../../symmetry_and_residuals/results/symmetry_search/symmetry_eigenspace_analysis.json): full results
- This note

## 5. Citations

- \cite{conner2023lowera}: Conner, Harper, Landsberg (2023), $\underline{R}(M_{\langle 233 \rangle}) = 14$
- \cite{landsberg2016geometry}: Landsberg, Michałek (2016), $\underline{R}(M_{\langle 3 \rangle}) \leq 20$
- \cite{yang2024ruling}: Yang (2024), symmetric exclusions at rank $\leq 21$
