# finite-order torsion-layer repair for termwise aligned inner symmetries

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Purpose

analysis tried to extend the characteristic-zero aligned-stratum exclusion from Lie-algebra elements to finite-order De Groote elements.  The first argument was not valid: finite roots of unity create multiplicative torsion layers not enumerated directly by the additive hyperplane arrangement, and unrestricted tensor-rank additivity for direct sums is false in general.  The valid repair is to analyze the torsion coarsening and to use rank additivity only in the protected Ja'Ja'--Takche situation where an actual direct-sum component has a small factor.

The repaired theorem below is about **noncentral finite-order inner/sandwich De Groote elements that fix every rank-one summand projectively**.  It does not cover De Groote elements with cyclic factor permutation or transpose components, and it does not settle finite-order symmetries that permute summands with central power.  The transverse rank-22 incidence remains open.

## Source status for the additivity input

The source retrieved in analysis, `research/research_record/staging/acquired/Tensor_rank_of_the_direct_sum_of_two_copies_of_2___2_matrix_d5429808a9eed0fe/part_001.md`, records:

- lines 121--124: Strassen's direct-sum additivity problem is false in general by Shitov;
- lines 128--129: Theorem 3.2.6, attributed to Ja'Ja'--Takche [JT86], states that for a two-summand tensor direct sum over an arbitrary field,
  \[
  R(p'\oplus p'')=R(p')+R(p'')
  \]
  if one of the six factor spaces \(A',A'',B',B'',C',C''\) has dimension at most 2;
- `part_002.md` lines 204 and 213 identify the references as Joseph Ja'Ja' and Jean Takche, *On the validity of the direct sum conjecture*, SIAM J. Comput. 15(4):1004--1020, 1986, and Yaroslav Shitov, *A counterexample to Strassen's direct sum conjecture*, Acta Math. 222(2):363--379, 2019.

The primary JT86 article was not fetched in this ARTIFACT; the theorem is currently supported by this retrieved source plus its bibliographic pointer.  Before final publication-level use, the exact JT86 field hypotheses should still be checked in the original paper.

The rectangular matrix-multiplication lower-bound input remains the analysis CHL closure:
\[
\underline R(M_{\langle 2,3,3\rangle})=14
\]
from CHL Theorem 1.5, read at `Knowledge/objects/papers/New-lower-bounds-for-matrix-multiplication-and--64a800eb2fe7--148396182a4c/object.md` lines 108--114.  Since ordinary rank is at least border rank and cyclic permutation of tensor factors preserves rank, this supplies the needed characteristic-zero lower bound for \((2,3,3)\) and its cyclic forms such as \((3,3,2)\).  Over an arbitrary characteristic-zero field, a putative shorter exact decomposition would live over a finitely generated extension of \(\mathbb Q\) and hence embed into \(\mathbb C\), contradicting the complex lower bound.

The declared weak analysis small-format input table is
\[
(2,3,3)\mapsto14,
\quad (2,2,3)\mapsto8,
\quad (2,2,2)\mapsto6.
\]
The CHL-improved table may use \((2,2,3)\mapsto10\), and one may separately use \(R(M_{\langle2,2,2\rangle})=7\), but the repaired theorem already works with the weak table.  The zero-margin input is \((2,3,3)\mapsto14\).

## Setup

Let \(K\) be a characteristic-zero field and work over an algebraic closure to diagonalize finite-order actions.  In the matrix-multiplication convention used in this investigation,
\[
T_{333}=\sum_{a,b,c=0}^2 e_{ab}\otimes e_{bc}\otimes e_{ca}.
\]
Consider an inner/sandwich De Groote element
\[
(X,Y,Z)\mapsto (P X Q^{-1},\; Q Y R^{-1},\; R Z P^{-1}).
\]
After diagonalizing the finite-order part, write the eigenvalues of \(P,Q,R\) as \(p_a,q_b,r_c\).  The three tensor-factor weights on the support triple \((a,b,c)\) are
\[
\alpha(a,b,c)=p_a/q_b,
\quad
\beta(a,b,c)=q_b/r_c,
\quad
\gamma(a,b,c)=r_c/p_a,
\]
with \(\alpha\beta\gamma=1\).

If a rank-one summand \(u_i\otimes v_i\otimes w_i\) is projectively fixed, equality of nonzero pure tensors implies
\[
u_i\in U_{\alpha_i},\qquad v_i\in V_{\beta_i},\qquad w_i\in W_{\gamma_i}
\]
for single factor weights.  The total product \(\alpha_i\beta_i\gamma_i\) need not be 1 for every summand; terms with total product different from 1 can only cancel inside zero target weight spaces.  Therefore one first groups all summands by the full triple \((\alpha,\beta,\gamma)\).  Projection to the target's nonzero weight spaces gives
\[
r\ge \sum_{\alpha,\beta} R\!\left(T_{\alpha,\beta,(\alpha\beta)^{-1}}\right).
\]
This is a weight-space counting inequality for termwise aligned decompositions, not a general direct-sum formula for the whole tensor.

## Torsion coarsening lemma

Choose a common order \(d\) for all sandwich eigenvalue ratios and write
\[
p_a=\zeta^{P_a},\quad q_b=\zeta^{Q_b},\quad r_c=\zeta^{R_c},
\qquad P_a,Q_b,R_c\in\{0,\dots,d-1\}.
\]
The multiplicative support block is determined by
\[
(P_a-Q_b,\;Q_b-R_c)\pmod d.
\]
Inside such a block, refine by the exact integer pair
\[
(P_a-Q_b,\;Q_b-R_c)\in\mathbb Z^2.
\]
These exact subblocks are additive weight blocks for the semisimple Lie-algebra calculation of analysis, using the chosen integer residues as weights.

**Lemma 1.**  Within any fixed multiplicative block, two different exact additive subblocks are disjoint in the original \(a\)-indices, disjoint in the original \(b\)-indices, and disjoint in the original \(c\)-indices.

**Proof.**  Suppose triples \((a,b,c)\) and \((a,b',c')\) in the same multiplicative block share the same \(a\).  Then
\[
P_a-Q_b\equiv P_a-Q_{b'}\pmod d,
\]
so \(Q_b=Q_{b'}\) because both are standard residue representatives in \(\{0,\dots,d-1\}\).  The second congruence gives \(R_c=R_{c'}\).  Therefore the exact integer pairs \((P_a-Q_b,Q_b-R_c)\) and \((P_a-Q_{b'},Q_{b'}-R_{c'})\) are equal, so the triples lie in the same exact additive subblock.  The same argument applies if the shared coordinate is \(b\) or \(c\).  Hence different exact subblocks share no original coordinate index.  \(\square\)

Because the matrix-multiplication factor coordinates are \((a,b)\), \((b,c)\), and \((c,a)\), disjointness of the original \(a,b,c\) index sets makes the corresponding sub-tensors an actual direct sum in all three tensor factors.

**Lemma 2.**  In one multiplicative block, at most one exact additive subblock has all three actual tensor-factor dimensions greater than 2.

**Proof.**  For an exact subblock let \(A_j,B_j,C_j\subset\{0,1,2\}\) be the original index sets it uses.  Its actual tensor-factor coordinate sets are subsets of \(A_j\times B_j\), \(B_j\times C_j\), and \(C_j\times A_j\).  If all three actual factor dimensions are greater than 2, then necessarily
\[
|A_j||B_j|>2,
\quad |B_j||C_j|>2,
\quad |C_j||A_j|>2.
\]
If one of \(|A_j|,|B_j|,|C_j|\) equals 1, the two adjacent inequalities force the other two cardinalities to be 3, so this subblock exhausts two complete original index sets and no other nonempty disjoint subblock can also be large.  If none equals 1, then all three cardinalities are at least 2; two pairwise-disjoint such subblocks would require at least four indices in each of \(A,B,C\), impossible inside \(\{0,1,2\}\).  Thus at most one subblock lacks a tensor factor of dimension at most 2.  \(\square\)

The computational guard [torsion_direct_sum_lemma_check.py](../code/torsion_direct_sum_lemma_check.py) checks this combinatorial statement for normalized residue patterns with \(d=2,\dots,12\): no violations, maximum three exact subblocks per multiplicative block, and maximum one subblock with all factor dimensions greater than 2.  This guard is not a substitute for the proof above.  It fixes \(P_0=Q_0=R_0=0\), which is complete for multiplicative support partitions but not for all choices of exact integer representatives; the written proof covers arbitrary representatives.

## Rank lower bound for a multiplicative block

Let a multiplicative block decompose into exact additive subblocks
\[
T_B = \bigoplus_{j=1}^m T_{B,j}
\]
in the actual tensor-factor sense.  By Lemma 2, all but possibly one component \(T_{B,j}\) has at least one tensor factor of dimension at most 2.  Apply the Ja'Ja'--Takche theorem inductively: peel off the small components one at a time.  At each ARTIFACT, the two-summand direct sum has one of its six factor spaces of dimension at most 2, so rank is additive for that ARTIFACT; the remaining summand can be arbitrary.  Therefore
\[
R(T_B)=\sum_{j=1}^m R(T_{B,j})
\ge \sum_{j=1}^m \operatorname{lb}(T_{B,j}),
\]
where \(\operatorname{lb}\) is any certified lower bound for the exact additive block.

Summing over all multiplicative blocks gives a lower bound equal to the analysis additive block-bound sum for the chosen integer residue weights.  If the inner/sandwich element is noncentral modulo the scalar center, these residue weights form a noncentral additive pattern.  analysis exhaustively enumerated the noncentral additive repeated-difference flats and, with the declared weak input table above, found histogram
\[
23:36,
\quad 24:108,
\quad 25:27,
\quad 27:6253.
\]
The analysis enumeration completeness is an input from [semisimple_arrangement_blockrank.py](../../deformation_and_incidence/code/semisimple_arrangement_blockrank.py) and [semisimple_arrangement_blockrank_v3_weaker_inputs.json](../../deformation_and_incidence/results/semisimple_arrangement/semisimple_arrangement_blockrank_v3_weaker_inputs.json); this analysis note does not rederive the full intersection-lattice enumeration.

## Repaired characteristic-zero statement

**Theorem (finite torsion, termwise aligned, inner version).**  Let \(K\) be a characteristic-zero field.  Let \(g\) be an inner/sandwich De Groote symmetry of \(T_{\langle3,3,3\rangle}\) whose image modulo the scalar center has finite order and is noncentral.  If an exact rank decomposition
\[
T_{\langle3,3,3\rangle}=\sum_{i=1}^r t_i
\]
has every rank-one Segre point \([t_i]\) fixed by \(g\), then \(r\ge23\).  In particular, no such length-\(\le22\) decomposition exists.

The proof is the weight-space splitting inequality, the torsion coarsening lemmas, the protected Ja'Ja'--Takche direct-sum additivity induction inside each multiplicative block, and the analysis additive block-rank enumeration with the CHL-supported \((2,3,3)\mapsto14\) input.

This theorem is a finite-order analogue of the analysis--24 Lie-algebra aligned-stratum result.  It is not obtained from the Lie algebra of a finite cyclic group; such a group is zero-dimensional.  It is obtained by the torsion-layer rank analysis above.

The proof does not use the full-\(UV\)-span refinement.  The theorem is compatible with that global framework, but the termwise aligned exclusion itself is stated for any exact decomposition satisfying the fixed-Segre-point hypothesis.

## Computational finite-layer scans

The general proof above makes finite-\(d\) scans auxiliary, but they are useful cross-checks and reveal the tight families.

Scripts and data:

- [d2_torsion_layers.py](../code/d2_torsion_layers.py)
- [torsion_layer_scan.py](../code/torsion_layer_scan.py)
- [torsion_layer_scan_fast.py](../code/torsion_layer_scan_fast.py)
- [torsion_direct_sum_lemma_check.py](../code/torsion_direct_sum_lemma_check.py)
- [d2_torsion_layer_analysis.json](../results/d2_torsion_layers/d2_torsion_layer_analysis.json)
- `workspace/data/d2_torsion_layers/torsion_layer_d3_scan.json`
- `workspace/data/d2_torsion_layers/torsion_layer_d4_scan.json`
- [torsion_layer_d2_scan_fast.json](../results/d2_torsion_layers/torsion_layer_d2_scan_fast.json) through `torsion_layer_d8_scan_fast.json`
- [torsion_direct_sum_lemma_check.json](../results/d2_torsion_layers/torsion_direct_sum_lemma_check.json)

Important scan outputs under the weak analysis input table:

| modulus | raw noncentral exponent patterns | canonical noncentral support partitions up to \(S_3^3\) | weak-table histogram | min |
|---:|---:|---:|---|---:|
| 2 | 504 | 7 | 23:288, 25:216 | 23 |
| 3 | 19,656 | 32 | 23:3402, 25:5832, 27:10422 | 23 |
| 4 | 262,080 | 43 | 23:17280, 25:46656, 27:198144 | 23 |
| 5 | 1,953,000 | 54 | 23:58500, 25:216000, 27:1678500 | 23 |
| 6 | 10,077,480 | 96 | 23:155520, 25:729000, 27:9192960 | 23 |
| 7 | 40,353,264 | 74 | 23:351918, 25:2000376, 27:38000970 | 23 |
| 8 | 134,217,216 | 94 | 23:709632, 25:4741632, 27:128765952 | 23 |

The d=2 scan is the most important repair target because involutions are common in published rank-23 families.  Its seven canonical noncentral support partitions have shapes:
\[
(18,9)\times72,
\quad (12,6,6,3)\times216,
\quad (9,6,6,6)\times216.
\]
The first two shapes already reach 23 by merged-block lower bounds and the small-format table.  The last shape is where the unsafe direct-block bound gives only 22; it reaches 25 only after decomposing the size-6 merged blocks into actual direct-sum components and applying the narrow JT86 theorem.  This is why the analysis unrestricted-additivity sentence had to be replaced rather than patched rhetorically.

## What remains open

The elementary power reduction is still valid: if a finite-order De Groote symmetry sends summands among themselves with permutation order \(d\), then its \(d\)-th power fixes each summand projectively.  If that power is a noncentral inner/sandwich element, the theorem above excludes length \(\le22\).  If that power is central, or if the relevant power lies in an outer cyclic/transpose component not handled by the inner proof, the termwise theorem gives no obstruction.  The remaining orbit-permuting case must use orbit structure directly.  For composite permutation order, the orbit count has the form
\[
22=f+\sum_{e\mid d,\ e>1} e\,m_e,
\]
and orbit points may be dependent; prime-order formulae are only special cases.

Thus the symmetry program now separates cleanly into:

1. termwise finite-order noncentral inner/sandwich symmetries in characteristic zero: excluded by the repaired theorem here;
2. finite-order orbit-permuting symmetries with central power: still open, with the analysis \(\mathbb F_2\) order-7 diagonal sandwich certificate as one finite-field named-family exclusion;
3. cyclic factor-permutation and transpose-containing De Groote elements: not covered by this inner/sandwich torsion proof and requiring their own weight/orbit formulation;
4. general transverse full-\(UV\)-rank incidence: still the main unresolved stratum for rank 22 versus 23.
