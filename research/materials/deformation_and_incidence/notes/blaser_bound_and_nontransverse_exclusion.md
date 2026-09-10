# Bläser bound for R(M_⟨3,3,2⟩) and nontransverse exclusion proposition

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## 1. The small-format lower bound R(M_⟨3,3,2⟩) ≥ 14

### Statement

**Theorem (Bläser 2003).** For integers m ≤ n,
$$
R(M_{\langle n,n,m\rangle}) \ge 2nm - m + 2n - 2.
$$
This bound holds over every field.

**Source.** M. Bläser, "On the complexity of the multiplication of matrices of small formats," *J. Complexity* 19 (2003), no. 1, 43–60.  MR 1951322 (2003k:68040).

**Secondary citation.** J.M. Landsberg, "New lower bounds for the rank of matrix multiplication," line 37, quotes this formula explicitly and references [2] = Bläser 2003. The paper is available as `Knowledge/objects/papers/New-lower-bounds-for-the-rank-of-matrix-multiplication--fe4c79cff1ba--b50c936262b4/object.md`.

### Application to M_⟨3,3,2⟩

Setting n = 3, m = 2:
$$
R(M_{\langle 3,3,2\rangle}) \ge 2(3)(2) - 2 + 2(3) - 2 = 12 - 2 + 6 - 2 = 14.
$$

### Verification context

- Bläser's proof uses the substitution method (Strassen's technique) combined with small-format structural arguments. The substitution method works over arbitrary fields: it deduces lower bounds on the bilinear complexity of a computation by restricting inputs (setting some variables to zero) and counting the surviving multiplication steps. Since it relies only on algebraic structure, not field topology, the bound R(M_⟨n,n,m⟩) ≥ 2nm − m + 2n − 2 is field-independent.

- The companion noncritical bounds R(M_⟨3,2,2⟩) ≥ 8 and R(M_⟨2,2,2⟩) ≥ 6 are verified internally by analysis's exterior-flattening script ([koszul_block_bounds.py](../../symmetry_and_residuals/code/koszul_block_bounds.py), output [koszul_block_bounds.json](../results/semisimple_arrangement/koszul_block_bounds.json)). These do not require external sources.

- Landsberg's Theorem 1.1 (same paper, line 34) gives a stronger bound for large n using Koszul flattenings, but for (3,3,2) Landsberg's bound with optimal p = 2 gives only (5/3)(3)(2) + 9 − (1+4·3)·3 = 10 + 9 − 39 = −20, which is not useful. The Bläser bound 14 is the operative lower bound for the small-format case.

## 2. Integrated nontransverse exclusion proposition

### Proposition (Nontransverse stratum exclusion)

**Setting.** Work over a field K of characteristic zero (or more generally any field where the nonsemisimple alignment lemma and Bläser's bound hold). Let T₃₃₃ ∈ K⁹ ⊗ K⁹ ⊗ K⁹ be the 3×3 matrix multiplication tensor. Consider a rank-r decomposition
$$
T_{333} = \sum_{i=1}^r u_i \otimes v_i \otimes w_i
$$
that is **full-span** (each factor set spans K⁹) and **termwise aligned** with a **noncentral** element (P,Q,R) ∈ gl₃³ of the matrix-multiplication stabilizer.

**Claim.** No such decomposition exists with r = 22.

### Proof structure

The proof combines three results:

**ARTIFACT A: Nonsemisimple alignment lemma (analysis).**
If the decomposition is full-span and termwise aligned with (P,Q,R), then the difference operators
$$
D_U(X) = P^TX - XQ^T, \quad D_V(Y) = Q^TY - YR^T, \quad D_W(Z) = ZR - PZ
$$
are semisimple on M₃(K). In particular, P, Q, R are simultaneously diagonalizable (after extending K if needed), and the nilpotent parts of P, Q, R vanish.

*Proof:* Termwise alignment means each u_i is an eigenvector of D_U, etc. Full span forces D_U to have a basis of eigenvectors, hence D_U is semisimple. Then D_U = L_{P^T} − R_{Q^T} semisimple implies P_n^TX = XQ_n^T for all X, which forces P_n = Q_n = 0. Similarly for the other pairs. See [nonsemisimple_alignment_lemma.md](nonsemisimple_alignment_lemma.md).

**ARTIFACT B: Semisimple weight-block decomposition.**
With P = diag(p₀,p₁,p₂), Q = diag(q₀,q₁,q₂), R = diag(r₀,r₁,r₂), each elementary matrix E_{ab} is a D_U-eigenvector with eigenvalue α = p_a − q_b, and similarly for D_V, D_W. Each rank-one summand u_i ⊗ v_i ⊗ w_i is a D_U ⊗ D_V ⊗ D_W eigenvector and must live in a single joint weight block. Hence the decomposition splits block-by-block:
$$
r = \sum_{\text{blocks } B} R(T_{333}|_B),
$$
where each block B is a coordinate sub-tensor of T₃₃₃ determined by the eigenvalue equality pattern.

**ARTIFACT C: Exact semisimple arrangement classification (analysis).**
The intersection lattice of all pairwise eigenvalue equalities in the 9 eigenvalue variables (p₀,...,p₂,q₀,...,q₂,r₀,...,r₂) was enumerated exactly over the rationals. There are 6425 flats total, of which 6424 are noncentral (at least one eigenvalue triple is not constant). For every noncentral flat, the block decomposition of T₃₃₃ was analyzed. Each block is either:

- A small flattening block (rank bounded by flattening), or
- A recognizable rectangular matrix-multiplication sub-tensor M_⟨a,b,c⟩ (rank bounded by the small-format table).

Using only the following lower-bound inputs:
- R(M_⟨3,3,2⟩) ≥ 14 (Bläser 2003; zero-margin critical input)
- R(M_⟨3,2,2⟩) ≥ 8 (exterior-flattening; internally verified)
- R(M_⟨2,2,2⟩) ≥ 6 (exterior-flattening; internally verified)
- All smaller blocks: flattening bounds

the minimum certified block-rank sum over all 6424 noncentral flats is **23**.

Distribution of certified sums: {23: 36, 24: 108, 25: 27, 27: 6253}.

Therefore, for every noncentral semisimple eigenvalue pattern, the block-rank sum is at least 23 > 22. No noncentral semisimple-aligned rank-22 decomposition of T₃₃₃ exists.

**Combining Steps A, B, C:** A full-span rank-22 decomposition aligned with a noncentral stabilizer element must be semisimple by (A), must decompose block-by-block by (B), and must have block-rank sum ≥ 23 by (C). Contradiction. ∎

### Scope and limitations

- This excludes the **nontransverse stratum** of the characteristic-zero rank-22 question, i.e., the stratum where the decomposition fiber is enlarged by a noncentral stabilizer element acting termwise.

- It does NOT prove R(T₃₃₃) ≥ 23. The following open layers remain:
  1. **Transverse full-span, full-UV-rank** decompositions (d = 2 gauge intersection, no termwise alignment with noncentral stabilizer)
  2. **Lower-UV-rank** decompositions where some UV columns are linearly dependent
  3. **Non-full-span** decompositions (some factor set has span < 9)

- The non-full-span case is quickly excluded: since T₃₃₃ has rank 9 in each flattening, any exact decomposition must have factors spanning each K⁹. So this case does not arise.

- The complete characteristic-zero rank-22 question therefore reduces to: transverse full-span/full-UV-rank charts + lower-UV-rank charts.

### Files

- Semisimple arrangement computation: [semisimple_arrangement_blockrank.py](../code/semisimple_arrangement_blockrank.py)
- Arrangement result (weaker inputs): [semisimple_arrangement_blockrank_v3_weaker_inputs.json](../results/semisimple_arrangement/semisimple_arrangement_blockrank_v3_weaker_inputs.json)
- Koszul block bounds: [koszul_block_bounds.json](../results/semisimple_arrangement/koszul_block_bounds.json)
- Nonsemisimple alignment lemma: [nonsemisimple_alignment_lemma.md](nonsemisimple_alignment_lemma.md)
- Landsberg/Bläser source: `Knowledge/objects/papers/New-lower-bounds-for-the-rank-of-matrix-multiplication--fe4c79cff1ba--b50c936262b4/object.md`
