# Trace-graded cyclic collapse to skeleton (10,4)

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Main result

**Theorem (trace-graded collapse under trace-parameter injectivity).** Let $f + 3m = 22$ be a pure cyclic rank-22 decomposition of $T_{\langle 3,3,3\rangle}$ over a characteristic-zero field, with free orbit representatives $(U_j,V_j,W_j)$ in $\mathfrak{gl}_3$. Write the diagonal restrictions as $\ell_{U_j}(X_0+sI)=\lambda_{U_j}(X_0)+a_js$ etc.; here $a_j,b_j,d_j$ are the actual independent-verification-record parameters. Equivalently, if $U_j=u_j+\alpha_jI$ with $u_j\in\mathfrak{sl}_3$, then $a_j=3\alpha_j$.

**(A) Mixed-trace vanishing.** The target's $I\wedge\Lambda^2(\mathfrak{sl}_3)$ component is zero: $T(I,B,C)=\operatorname{tr}(BC)$ is symmetric, so the relevant alternating component is proportional to $\operatorname{tr}([B,C])=0$. Cubes contribute nothing to the antisymmetric part. Therefore the trace-parameter map satisfies
$$\Psi(a,b,d)=\sum_{j=1}^m\bigl(a_jv_j\wedge w_j+b_jw_j\wedge u_j+d_ju_j\wedge v_j\bigr)=0\in\Lambda^2(\mathfrak{sl}_3).$$

**(B) Traceless case.** If all free orbit traces vanish ($a_j=b_j=d_j=0$ for all $j$), substitute $X=X_0+sI$ with $\operatorname{tr}(X_0)=0$ in the diagonal identity. The free orbit terms are $s$-independent. The $s^1$ coefficient gives
$$\operatorname{tr}(X_0^2)=\sum_{i=1}^f c_i\lambda_i(X_0)^2\quad\text{on }\mathfrak{sl}_3,$$
where $c_i=\operatorname{tr}(L_i)$ and $\lambda_i=\operatorname{tr}(L_i^TX_0)$. The trace form on $\mathfrak{sl}_3$ has integer rank $8$ (Gram determinant $\pm3$, verified). Each $c_i\lambda_i^2$ is rank $\le1$, so $f\ge8$, hence $3m\le14$ and $m\le4$.

**(C) Collapse.** Combined with the Cartan prehomogeneity theorem ($m\ge4$, analysis), pure cyclic rank-22 under the explicit hypothesis $\ker\Psi=0$ (hence traceless free orbits) reduces to the single skeleton $(f,m)=(10,4)$.

## BILR positive control (exact integer verification)

The BILR $Z_4\times Z_3$ rank-23 scheme has $f=11$ cubes and $m=4$ free orbits. All verified over $\mathbb Z$:

| Condition | Result |
|-----------|--------|
| Mixed-trace rank (28×12 map) | 12 (injective, forces all traces zero) |
| $\sum c_i\lambda_i^2=\operatorname{tr}(X_0^2)$ over $\mathbb Z$ | True (entrywise exact) |
| $\sum c_i^2\lambda_i=0$ over $\mathbb Z$ | True |
| $\sum c_i^3=3$ | True ($7(1)^3+4(-1)^3=3$) |
| Cubes with nonzero trace | 11/11 (7 with $c=+1$, 4 with $c=-1$) |
| Active form span rank in $\mathfrak{sl}_3^*$ | 8 (full) |
| Pairwise plane intersections $\dim(P_i\cap P_j)$ | All 6 pairs: 0 |
| Killing form signature (over $\mathbb R$) | $(5,3)$, det $=-3$ |

The BILR decomposition of the Killing form: 7 positive-trace cubes contribute rank-one positive terms; 4 negative-trace cubes contribute rank-one negative terms. Together they produce the exact rank-8 Killing form with 3 cancellation dimensions (kernel dim = $11-8=3$ for the 11 forms in 8-dim space).

## Corrected status of tracelessness on the rank-4 fiber (analysis repair)

The traceless theorem is conditional on the mixed-trace map
\[
\Phi_{(P_j)}:\bigoplus_j\Lambda^2(P_j)\to\Lambda^2(\mathfrak{sl}_3)
\]
having zero kernel, where \(P_j=\langle u_j,v_j,w_j\rangle\). analysis corrected the interpretation of the sampling data: internal recombination of each ordered triple inside its plane leaves the planes \(P_j\) fixed, and global adjoint conjugates all planes by a single \(\mathrm{PGL}_3\) element. Therefore the previously recorded 40/40 rank-12 samples are not evidence for other components of the rank-4 exterior fiber.

What is rigorously established is component-local: at the BILR four-plane configuration, \(\Phi\) has rank 12, so free traces vanish on this component under these plane-preserving/PGL motions. Other components, if they exist, require a separate exact classification by plane invariants such as restricted determinant cubic, restricted Killing conic, subalgebra flag, and pairwise intersections. Also, pairwise absence of shared 2-planes is not by itself a proof that \(\Phi\) has rank 12; it excludes only the simplest two-term kernel relations, not possible four-term relations.
## Moment conditions for the (10,4) skeleton

For any pure cyclic rank-22 $(10,4)$ decomposition with traceless free orbits, the 10 fixed-cube forms (with scalar coefficients absorbed when the field permits, or with weights included separately) must satisfy:

1. $\sum_{i=1}^{10} c_i\lambda_i^2=\operatorname{tr}(X_0^2)$ on $\mathfrak{sl}_3$ (rank-8 Killing form)
2. $\sum_{i=1}^{10} c_i^2\lambda_i=0$ in $\mathfrak{sl}_3^*$
3. $\sum_{i=1}^{10} c_i^3=3$

where $c_i=\ell_{L_i}(I)$. At least nine essential nodes with $c_i\ne0$ and nonzero restricted form are needed: exactly eight would form a basis and make $\sum w_i\mu_i=0$ impossible with nonzero weights. This is a $\mathrm{PGL}_3$-equivariant condition on the cube configuration, but it must still be coupled to the exterior decomposition and residual cubic.

## Non-traceless branch (analysis correction for $m\ge5$)

For $m\ge5$, the trace-graded argument above does not close the skeletons $(7,5),(4,6),(1,7)$. Without tracelessness the $s$-linear identity is
\[
\operatorname{tr}(X_0^2)=\sum_i c_i\lambda_i^2+\sum_j q_j,\qquad
q_j=a_j\lambda_{V_j}\lambda_{W_j}+b_j\lambda_{W_j}\lambda_{U_j}+d_j\lambda_{U_j}\lambda_{V_j}.
\]
In the $(\lambda_U,\lambda_V,\lambda_W)$ coordinates, the symmetric matrix of a single $q_j$ is hollow; in characteristic zero its rank is $0$, $2$, or $3$, never $1$. Thus an extension of the $f\ge8$ contradiction would require a bound on $\operatorname{rank}\sum_j q_j$ compatible with the cube count: rank $0$ for $m=5$, at most $3$ for $m=6$, at most $6$ for $m=7$ in the corresponding contradiction attempt.

There is also a dependent-traceless-part branch: if $u_j,v_j,w_j$ are linearly dependent, the orbit contributes no Cartan volume, $\Lambda^2(P_j)$ has dimension at most one, and the mixed-trace equation may have a two-parameter set of nonzero trace solutions. For example $w=u+v$ gives the relation $d=a+b$ and a generically rank-2 quadratic $q_j$. Therefore the $m\ge5$ cases require an exact treatment of decomposable-bivector relations together with the full $s^2$ and $s^3$ equations
\[
\sum_i c_i^2\lambda_i+\sum_j(a_jb_j\lambda_{W_j}+a_jd_j\lambda_{V_j}+b_jd_j\lambda_{U_j})=0,
\]
\[
\sum_i c_i^3+3\sum_j a_jb_jd_j=3.
\]

## Files

- [trace_grading_collapse.py](../code/trace_grading_collapse.py): main verification script
- [trace_grading_verification.json](../results/trace_grading/trace_grading_verification.json): modular verification
- [cube_moment_analysis.py](../code/cube_moment_analysis.py): integer cube moments
- [cube_moment_analysis.json](../results/trace_grading/cube_moment_analysis.json): integer results

## repair artifacts

- [moment_cubature_instrument.py](../../relaxations_and_cuts/code/moment_cubature_instrument.py) and [moment_cubature_instrument.json](../../relaxations_and_cuts/results/moment_cubature/moment_cubature_instrument.json): normalized BILR cubature control, k=8 active-cube impossibility, and BILR deletion controls.
- [cubic_residual_control.py](../../quotient_cores/code/cubic_residual_control.py) and [cubic_residual_control.json](../../relaxations_and_cuts/results/moment_cubature/cubic_residual_control.json): exact normalized cubic residual identity for BILR.
- [nontraceless_branch_checks.py](../../quotient_cores/code/nontraceless_branch_checks.py) and [nontraceless_branch_algebra.json](../../relaxations_and_cuts/results/moment_cubature/nontraceless_branch_algebra.json): hollow-matrix rank calculation and dependent-orbit branch showing why m>=5 remains open.
- [plane_invariant_extractor.py](../../quotient_cores/code/plane_invariant_extractor.py) and [bilr_plane_invariants.json](../results/plane_invariants/bilr_plane_invariants.json): BILR four-plane invariants and exact component-local mixed-trace rank 12.
