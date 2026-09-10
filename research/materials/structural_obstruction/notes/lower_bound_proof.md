# Lower bound route for 3x3 matrix multiplication over F2

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

This note records the current proof as a mathematical argument with explicit machine-verified finite inputs.  It is research material for continued verification, not a final publication-ready manuscript.

## Tensor convention

The multiplication tensor is indexed by
\[
T[3i+j,\,3j+k,\,3i+k]=1\qquad (0\le i,j,k<3),
\]
so the trilinear form is
\[
(A,B,C)\longmapsto \operatorname{tr}(A B C^T).
\]
A rank-one summand is written as \(A_t\otimes B_t\otimes C_t\), with the three factors regarded as \(3\times 3\) matrices over \(\mathbb F_2\).

## Finite inputs used by the proof

The proof uses Wang's certified lower-bound table for quotient tensors \(T/W\) in the A-slot.  The replayed receipt is
`data/wang_f2_lb20/verify_receipt.json`, with verified certificate
`data/wang_f2_lb20/cert_matrix_q02_n333.pb.txt` and SHA256
`25595a883ce877eecd802139ff4e07646e154b2797ad6fe7f9ec737ab0c6135d`.
The expanded lookup table is
`data/wang_f2_lb20/wang_subspace_lut.pkl`, SHA256
`4704acba23a97d40aa65d5a65222dcb679461fdccf3e41dbeed2a634894a3b33`.

For a subspace \(W\le \mathbb F_2^9\), let \(L(W)\) denote the lower bound in this table.  If a length-\(n\) decomposition has \(m(W)\) A-factors lying in \(W\), then quotienting by \(W\) leaves at most \(n-m(W)\) summands.  Hence
\[
m(W)\le n-L(W).\tag{1}
\]
This is the only way the Wang table is used.

The extra finite inputs beyond Wang's original rank-20 certificate are the eight dimension-two raises.  For the dimension-two orbit representatives 484--491, the original table has \(L(W)=18\), and the inherited occupation system at length 18 is infeasible.  Equivalently, if
\[
x_q\in\mathbb Z_{\ge0},\qquad \sum_{q\in(\mathbb F_2^9/W)\setminus0}x_q=18,
\]
and for every nonzero proper quotient subspace \(V/W\)
\[
\sum_{q\in (V/W)\setminus0}x_q\le 18-L(V),\tag{2}
\]
then no integer solution exists.  analysis independently rebuilt these eight systems directly from the table and found exact row agreement with the older builder.  analysis also projected a verified rank-23 decomposition modulo each \(W\), dropped terms killed by the quotient, and scanned the resulting multiset through the same independently rebuilt rows at its projected length; all eight scans have zero violations.  The edge test at length 19 is feasible for all eight systems, including orbit 491 after the longer run.

Important files:

- independent row reconstruction and positive controls: [independent_semantics_summary.json](../../finite_certification/results/dim2_independent/independent_semantics_summary.json);
- orbit 491 length-19 witness run: [orbit491_target19_long.json](../../finite_certification/results/dim2_independent/orbit491_target19_long.json);
- CP-SAT and HiGHS integer infeasibility: [cpsat_certificate_summary.json](../../finite_certification/results/dim2_certificates/cpsat_certificate_summary.json);
- DRAT-checked CNF files for all eight dimension-two raises: [summary.json](../../finite_certification/results/dim2_cnf_cert_all/summary.json) and the eight orbit subdirectories;
- end-to-end bundle verification, including byte-for-byte CNF regeneration and all eight DRAT rechecks: [bundle_check_regenerate.json](../../finite_certification/results/bundle_check/bundle_check_regenerate.json).

## Proof

Assume for contradiction that
\[
T=\sum_{t=1}^{20} A_t\otimes B_t\otimes C_t
\]
is an exact decomposition over \(\mathbb F_2\), with no zero summands.

### 1. The A-split flattening forces at least four high-rank A-factors

Split the A-coordinate as row and column indices.  The resulting flattening \(P=\Phi_A(T)\) is a \(27\times27\) permutation matrix, hence \(\operatorname{rank}P=27\).  For a summand,
\[
\Phi_A(A_t\otimes B_t\otimes C_t)
  = A_t\otimes \operatorname{vec}(B_t)\operatorname{vec}(C_t)^T,
\]
so its rank is \(\operatorname{rank}A_t\).  Therefore
\[
27=\operatorname{rank}P\le \sum_{t=1}^{20}\operatorname{rank}A_t.
\]
Writing \(e_t=\operatorname{rank}A_t-1\in\{0,1,2\}\), we obtain \(\sum e_t\ge7\).  Three terms contribute at most six, so at least four A-factors have rank at least two.  Call these factors high.

### 2. No A-direction repeats

For every line \(\langle a\rangle\), the table has \(L(\langle a\rangle)=19\).  Applying (1) with \(n=20\), at most one A-factor can lie in any such line.  Since \(\mathbb F_2\) has only one nonzero scalar, the twenty nonzero matrices \(A_t\) are pairwise distinct.

### 3. High-rank pairs have rank-one differences

Let \(A_s,A_t\) be two distinct high factors and set \(W=\langle A_s,A_t\rangle\).  If \(A_s+A_t\) also has rank at least two, then all three nonzero elements of \(W\) have rank at least two.  The dimension-two orbit classification shows that these are exactly orbits 484--491.  The eight raises give \(L(W)\ge19\) in this case.  But \(W\) contains both \(A_s\) and \(A_t\), so \(m(W)\ge2\), contradicting (1) with \(n=20\) and \(L(W)\ge19\).  Hence
\[
\operatorname{rank}(A_s+A_t)=1
\]
for every pair of high factors.

### 4. Pairwise rank-one differences force one affine row or column coset

Let \(H\) be the set of high factors.  We know \(|H|\ge4\), its elements are distinct, and all pairwise differences have rank one.  Fix \(a,b,c\in H\).  Write
\[
a+b=u_1v_1^T,
\qquad a+c=u_2v_2^T.
\]
Then
\[
b+c=(a+b)+(a+c)=u_1v_1^T+u_2v_2^T
\]
has rank one.  Over any field, the sum of two nonzero rank-one matrices has rank at most one only when the two matrices share a left factor or share a right factor.  Thus either \(u_1,u_2\) are dependent or \(v_1,v_2\) are dependent.  Over \(\mathbb F_2\), nonzero dependent vectors are equal.

If the triple \(a,b,c\) has common left vector \(u\), then \(b=a+u w_b^T\), \(c=a+u w_c^T\).  If it has common right vector \(v\), then \(b=a+w_bv^T\), \(c=a+w_cv^T\).  A triple cannot be genuinely both types unless two of its points coincide: two independent row parameters and two independent column parameters would produce a two-dimensional rank-one difference space, while equality of both parameters collapses a point.

Now take a fourth point \(d\in H\).  If \(a,b,c\) are column type with common left vector \(u\), write \(a+d=u'v'^T\).  Since \(b+d=(a+b)+(a+d)\) and \(c+d=(a+c)+(a+d)\) both have rank one, the rank-one sum test gives either \(u'=u\) or \(v'\) equals the row parameter for \(b\), and either \(u'=u\) or \(v'\) equals the row parameter for \(c\).  The two row parameters are distinct, so \(u'=u\).  Thus \(d\) lies in the same column-type affine coset.  The row-type case is identical after transposition.  Hence all high factors lie in
\[
p+u(\mathbb F_2^3)^T
\quad\text{or}\quad
p+\mathbb F_2^3 v^T.
\tag{3}
\]

The tensor automorphism
\[
(A,B,C)\longmapsto (A^T,C,B)
\]
preserves \(\operatorname{tr}(ABC^T)\).  Therefore the row-type case may be transposed into the column-type case.  It is enough to analyze column type.

### 5. The affine-plane caps force exactly one rank-two and three rank-three high factors

Use the \(\operatorname{GL}_3\times\operatorname{GL}_3\) symmetries to normalize the column-type coset to
\[
p+e_1(\mathbb F_2^3)^T.
\]
Adding \(e_1w^T\) changes only the first row.  Let \(D\) be the lower \(2\times3\) block of \(p\).  If \(\operatorname{rank}D\le1\), then no coset element has rank three and at most six coset elements have rank two; their total excess is at most six, contradicting \(\sum e_t\ge7\).  Hence \(\operatorname{rank}D=2\).  In this case four of the eight coset elements have rank two and four have rank three, according to whether the first row lies in the row span of \(D\).

Let
\[
S=\langle p, e_1e_1^T,e_1e_2^T,e_1e_3^T\rangle.
\]
Its hyperplanes consist of the rank-one family
\(R=\langle e_1e_1^T,e_1e_2^T,e_1e_3^T\rangle\), which has table value 15, and fourteen other hyperplanes corresponding to the fourteen affine planes in \(\mathbb F_2^3\).  The table gives value 17 for each of these fourteen hyperplanes.  Thus (1) with \(n=20\) says each affine plane contains at most three A-factors.

Every five-point subset of \(\mathbb F_2^3\) contains a four-point affine plane.  Therefore the high-factor set has size at most four.  Since analysis gives at least four, it has exactly four elements.

The four rank-three coset elements form an affine plane, so at most three high factors are rank three.  With sixteen remaining A-factors of rank one, the rank sum is
\[
16 + 2h_2 + 3h_3 = 16+2(4-h_3)+3h_3=24+h_3.
\]
It must be at least 27, hence \(h_3\ge3\).  Consequently \(h_3=3\), \(h_2=1\), and
\[
\sum_{t=1}^{20}\operatorname{rank}A_t=16+2+3+3+3=27.
\tag{4}
\]

### 6. Saturation of the A-split flattening contradicts three invertible A-factors

Let
\[
M_t=\Phi_A(A_t\otimes B_t\otimes C_t),\qquad P=\sum_{t=1}^{20}M_t.
\]
Equation (4) gives
\[
\sum_t\operatorname{rank}M_t=\operatorname{rank}P.
\]
Thus equality holds in rank subadditivity.  The column spaces of the \(M_t\) form a direct sum equal to the target space, and their row spaces form a direct sum equal to the source dual space.  For any vector \(x\), the vector \(M_sx\) lies in the \(s\)-th column summand.  If \(z=P^{-1}M_sx\), then
\[
Pz=\sum_t M_tz=M_sx
\]
has a unique direct-sum decomposition, so \(M_tz=0\) for \(t\ne s\) and \(M_sz=M_sx\).  Therefore
\[
M_tP^{-1}M_s=\delta_{ts}M_t.
\tag{5}
\]

For the present tensor convention, direct index multiplication gives
\[
M(A_t,B_t,C_t)P^{-1}M(A_s,B_s,C_s)
=
M(A_tB_sC_t^T A_s,\,B_t,\,C_s).
\tag{6}
\]
Take a summand with \(A_t\) invertible.  From (5) and (6) with \(s=t\),
\[
A_tB_tC_t^TA_t=A_t,
\]
so
\[
B_tC_t^T=A_t^{-1}.
\]
Hence \(B_t\) and \(C_t\) are invertible.  If \(A_t\) and \(A_s\) are two distinct invertible A-factors, then the off-diagonal equation in (5) and (6) gives
\[
A_tB_sC_t^TA_s=0.
\]
But \(A_t,A_s,B_s,C_t\) are all invertible, impossible.  Thus a saturated decomposition has at most one invertible A-factor.

analysis forced three invertible A-factors.  This contradiction excludes length 20 decompositions.  Therefore
\[
R_{\mathbb F_2}(T_{\langle3,3,3\rangle})\ge21.
\]

## Certificate status

The eight dimension-two raises now have independently replayable proof files.  Current support for the raises consists of:

1. independent semantic reconstruction of all eight row systems, row-by-row agreement with the older builder, target-18 infeasibility by CP-SAT, and successful projection scans of a verified rank-23 decomposition;
2. target-19 feasibility for all eight systems, showing that the inherited occupation layer changes exactly between lengths 18 and 19;
3. CP-SAT and HiGHS integer infeasibility for all eight target-18 systems;
4. complete safe-DFS zero-solution runs for the seven systems whose singleton caps are 0/1 only;
5. DRAT-checked CNF files for all eight systems, including orbit 489 with its multiplicity-two quotient direction;
6. end-to-end bundle verification with byte-for-byte CNF regeneration and all eight DRAT rechecks in [bundle_check_regenerate.json](../../finite_certification/results/bundle_check/bundle_check_regenerate.json).

The next research work is independent reproduction by research_record and external-style review of the proof-to-code correspondence before moving to final expression.
