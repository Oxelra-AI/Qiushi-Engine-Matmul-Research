# transpose complementary sector and corrected skeleton targeting

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Purpose

analysis opened the transpose involution
\[
\tau(u,v,w)=(u^T,w^T,v^T),\qquad \tau(X,Y,Z)=(X^T,Z^T,Y^T),
\]
but over-recorded the Gram construction as a lower bound.  This ARTIFACT rebuilt the \(\tau\)-split with a fixed coefficient convention, checked it against the standard 27-term multiplication scheme, and separated the two exact subspace problems that must replace a blind nonlinear search on all 378 equations.

The pairing convention used in all analysis scripts is entrywise
\[
\ell_u(X)=\sum_{i,j}u_{ij}X_{ij}.
\]
With this convention, for a skew matrix \(A^T=-A\),
\[
\ell_{u^T}(A)=-\ell_u(A).
\]

## 1. Exact \(270+108\) split and `naive_27` convention check

Let \(X=S+A\) with \(S^T=S\), \(A^T=-A\), and identify the third factor with the transpose of the second on the \(\tau\)-fixed variables.  The invariant space decomposes as
\[
(K^9)^{\otimes3}_+
 =\operatorname{Sym}_3\otimes \operatorname{Sym}^2(K^9)
 \oplus \Lambda^2K^3\otimes \Lambda^2(K^9),
\]
with dimensions
\[
6\cdot45+3\cdot36=270+108=378.
\]
The following decomposition is used after identifying the third factor with the transposed second factor, and it requires \(\operatorname{char}K\ne2\) for the symmetric/skew splitting.  The exact check in [transpose_complement.py](../code/transpose_complement.py) expands the standard 27-term scheme into its \(9\) fixed \(\tau\)-terms and \(9\) free two-orbits.  After including the factor 2 for the off-diagonal symmetric basis \(E_{ij}+E_{ji}\), both sectors match exactly:

- `gram_matches_target=true`, `max_gram_error=0.0`;
- `anti_matches_target=true`, `max_anti_error=0.0`.

This is the guard against the transpose/row-major convention mistakes that affected earlier finite-field and Hessian computations.

## 2. Complementary sector entry problem

For \(A^T=-A\), fixed \(\tau\)-terms vanish in the complementary sector.  A free orbit represented by \((u,v,w)\) contributes
\[
\ell_u(A)\left(\ell_v(Y)\ell_w(Z)-\ell_{w^T}(Y)\ell_{v^T}(Z)\right).
\]
After identifying the \(Z\)-variable with the transpose coordinate in the second factor, each free orbit supplies one decomposable bivector in \(\Lambda^2(K^9)\).  The target rows are
\[
\theta_{01}=-\sum_{k=0}^2 e_{0k}\wedge e_{1k},\quad
\theta_{02}=-\sum_{k=0}^2 e_{0k}\wedge e_{2k},\quad
\theta_{12}=-\sum_{k=0}^2 e_{1k}\wedge e_{2k}.
\]
Equivalently, with the wedge-coordinate convention in the script,
\[
T_{\rm anti}(A_{ab};Y,Z)=\operatorname{tr}(A_{ab}YZ)
=-\sum_{k=0}^2\bigl(Y_{ak}z_{bk}-Y_{bk}z_{ak}\bigr).
\]
The informal formula \(\sum_k\langle A,y^{(k)}\wedge z_{(k)}\rangle\) is valid only after choosing a matching exterior pairing/sign convention; the stored target rows above are the authoritative normalization.  The three column copies share the skew \(A\)-factor.

Let \(m_0\) be the least number of decomposable bivectors \(p_j\wedge q_j\in\Lambda^2K^9\) whose span contains the three-dimensional space \(L_{\rm anti}=\langle\theta_{01},\theta_{02},\theta_{12}\rangle\).  The current exact bounds are
\[
7\le m_0\le 9\qquad(\operatorname{char}K\ne2).
\]

Evidence:

- The flattening ranks of \(T_{\rm anti}\in K^3\otimes K^9\otimes K^9\) are \((3,9,9)\), so conciseness gives ordinary rank at least 9.  Since one \(\tau\)-free orbit has ordinary \((Y,Z)\)-rank at most 2, this first gives \(m_0\ge5\).
- Exterior flattenings \(A^*\otimes\Lambda^qK^9\to\Lambda^{q+2}K^9\) and the bigraded variants \(\Lambda^sK^3\otimes\Lambda^qK^9\to\Lambda^{s+1}K^3\otimes\Lambda^{q+2}K^9\) were computed exactly over \(p=1000003\).  Their best bound is also \(m_0\ge5\); no stronger bound was obtained from these particular flattenings.
- review suggested, and [anti_Awedge_flattening.py](../../quotient_cores/code/anti_Awedge_flattening.py) verified, an \(A\)-factor exterior flattening
  \[
  F_T:A\otimes W^*\to\Lambda^2A\otimes W,
  \qquad e_s\otimes\beta\mapsto\sum_r(e_r\wedge e_s)\otimes\theta_r(\beta).
  \]
  For one structured term \(c\otimes(p\wedge q)\), the image lies in \((c\wedge A)\otimes\langle p,q\rangle\), so its rank is at most \(4\).  For the analysis target, \(F_T\) has rank \(27\) over \(p=1000003\); [anti_Awedge_integer.py](../../quotient_cores/code/anti_Awedge_integer.py) then computed the exact integer determinant \(8=2^3\).  Symbolically this is the invertible operator \(V\mapsto V^T-\operatorname{tr}(V)I\) on \(M_3\) tensored with the column identity.  Hence \(m_0\ge\lceil27/4\rceil=7\) in characteristic not 2.
- The columnwise decomposition
  \(
  \theta_{ij}= -\sum_{k=0}^2 e_{ik}\wedge e_{jk}
  \)
  uses nine decomposable bivectors, giving \(m_0\le9\).

The single-copy determinant tensor rank is known to be 5 over every field by Krishna--Makam \cite{krishna2018tensor}; this supports the ordinary tensor-rank scale of the column summands but is not the sharp structured-bivector number for \(m_0\).

## 3. Coupling with the Gram sector is only through the \((v,w)\) pairs
Once the fixed square forms and free \((v_j,w_j)\) pairs are chosen, both sectors are linear in the \(u\)-data:

- symmetric parts \(u_j^{\rm sym}\), together with fixed terms, choose linear combinations of the Gram quadrics;
- skew parts \(u_j^{\rm anti}\) choose linear combinations of the free bivectors.

Thus the correct computational object is a pair-selection/subspace-containment problem in the \((v,w)\) data, followed by exact linear solving for \(u\).  The cancelled numerical least-squares task `s61_t14_tool1` reached only an untrusted partial residual for \(m=5\); it should not be used.  The project has already seen noncompact border-rank residuals in earlier analysis, 37, and 55, so direct minimization of the 378 equations is a poor guide.
The new \(m_0\ge7\) removes the rank-22 skeletons \((12,5)\) and \((10,6)\) inside this standard \(\tau\)-orbit ansatz; the remaining skeletons are \((8,7),(6,8),(4,9),(2,10),(0,11)\), subject also to the Gram containment problem.

## 4. Literal \((6,8)\) row-norm polarization route is obstructed

The review suggested starting from the analysis polarization split
\[
\|hY\|^2=(hY_0+i hY_1)(hY_0-i hY_1)+(hY_2)^2
\]
for six row combinations \(h\), giving six fixed squares and six free products, then using two further free orbits for the complementary sector.

The exact component calculation in [component_obstruction.py](../../quotient_cores/code/component_obstruction.py) shows that this literal construction cannot work.  For \(W=U\otimes C\),
\[
\Lambda^2W=(\Lambda^2U\otimes\operatorname{Sym}^2C)\oplus(\operatorname{Sym}^2U\otimes\Lambda^2C).
\]
The complementary target lies in \(\Lambda^2U\otimes\operatorname{Sym}^2C\), with rank 3.  The six free bivectors in the row-norm polarization have the form
\[
(h\otimes(c_0+i c_1))\wedge(h\otimes(c_0-i c_1))
\]
and therefore lie entirely in \(\operatorname{Sym}^2U\otimes\Lambda^2C\).  Two additional free orbits can contribute at most a two-dimensional projection to \(\Lambda^2U\otimes\operatorname{Sym}^2C\), so this exact six-plus-two completion cannot satisfy the complementary sector.

This does not exclude all \((6,8)\) skeletons: a different Gram realization could use free products with nonzero projection to \(\Lambda^2U\otimes\operatorname{Sym}^2C\).  It only removes the most immediate row-norm split.

## 5. Corrected status of the Gram number

Let \(N_G\) be the least number of reducible quadrics in \(\operatorname{Sym}^2(K^9)\) whose span contains the six-dimensional Gram space.  analysis produced an exact construction with \(N_G\le12\) over fields containing \(\sqrt{-1}\).  analysis patched [transpose_layer_analysis.md](transpose_layer_analysis.md): this is not a lower bound.  Failed random trials and the fact that all twelve displayed products are essential inside that displayed construction do not prove \(N_G=12\), and do not remove the all-free \((0,11)\) skeleton.

The Arrigoni--Maggioli--Massini--Rodolà paper \cite{arrigoni2021efficiently} confirms that Dumas--Pernet--Sedoglavic type \(AA^T\) algorithms use skew-orthogonal-field structure, but the source read in this ARTIFACT does not give an exact 3-by-3 bilinear optimum.  The exact \(N_G\) for \(3\times3\) remains to be established or sourced before skeletons are removed by Gram data.

## 6. Known rank-23 transpose-like context

Literal standard-form \(\tau\)-fixedness is not the same as being invariant under a transpose-like De Groote symmetry up to sandwich and cyclic variant.  The BILR source \cite{ballard2018geometry} explicitly states:

- convenient transpose symmetries do not appear to be compatible with standard cyclic symmetries in known minimal decompositions (line 336 in the local object);
- the \(Z_4\times Z_3\) scheme has no transpose-like symmetry by incidence-graph frequencies (Proposition 5.1 proof, line 415);
- the Laderman-\(Z_3\) family is presented using a \(\mathbb Z_3\rtimes\mathbb Z_2^\zeta\) orbit (lines 667--678).

Therefore analysis's literal statement that no known rank-23 scheme is \(\tau\)-invariant should be read only as standard-coordinate fixedness.  Any novelty or occupancy statement for the transpose layer must be made up to sandwich/cyclic transpose-like symmetry.

## 7. Exact files

- [transpose_complement.py](../code/transpose_complement.py)
- [transpose_complement_entry.json](../results/transpose_complement/transpose_complement_entry.json)
- [component_obstruction.py](../../quotient_cores/code/component_obstruction.py)
- [component_obstruction_f6m8_polarization.json](../results/transpose_component/component_obstruction_f6m8_polarization.json)
- [anti_koszul_flattening.py](../code/anti_koszul_flattening.py)
- [anti_koszul_flattening.json](../results/transpose_component/anti_koszul_flattening.json)
- [anti_bigraded_flattening.py](../../quotient_cores/code/anti_bigraded_flattening.py)
- [anti_bigraded_flattening.json](../results/transpose_component/anti_bigraded_flattening.json)
- [anti_Awedge_flattening.py](../../quotient_cores/code/anti_Awedge_flattening.py)
- [anti_Awedge_flattening.json](../results/transpose_component/anti_Awedge_flattening.json)
- [anti_Awedge_integer.py](../../quotient_cores/code/anti_Awedge_integer.py)
- [anti_Awedge_integer_det.json](../results/transpose_component/anti_Awedge_integer_det.json)
- [naive_subset_feasibility.py](../../quotient_cores/code/naive_subset_feasibility.py)
- [naive27_rank22_subset_entry_feasibility.json](../results/transpose_complement/naive27_rank22_subset_entry_feasibility.json)

## 8. Next mathematical work

The next useful execution is not residual minimization.  It is to determine whether \(m_0=7,8,\) or \(9\), or produce exact configurations for \(m<9\), and to combine those configurations with Gram containment through the shared \((v,w)\) pairs.  Promising concrete objects:

1. classify or search the plane \(L_{\rm anti}\subset\Lambda^2K^9\) inside spans of \(m\) decomposable bivectors, especially \(m=5,6,7,8\);
2. derive additional lower bounds beyond the current exterior flattenings, using the constant-rank-six plane structure and bounded-rank alternating matrix-space literature;
3. build an exact modular linear-feasibility oracle: given candidate free pairs and fixed square forms, solve for all symmetric/skew \(u\)-coefficients and then expand back to the full 729 Brent identities;
4. explore non-row-norm Gram constructions whose free bivectors have nonzero \(\Lambda^2U\otimes\operatorname{Sym}^2C\) projection, since the literal row-norm split cannot support \((6,8)\).
