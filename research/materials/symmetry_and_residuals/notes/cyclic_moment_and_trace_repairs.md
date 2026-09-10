# cyclic trace-grading repairs and moment instrument

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Reliable cyclic theorem after the repair

For a characteristic-zero pure cyclic rank-22 decomposition with skeleton
\[
f+3m=22,
\]
write the free orbit linear forms on diagonal matrices as
\[
\ell_{U_j}(X_0+sI)=\lambda_{U_j}(X_0)+a_js,
\quad
\ell_{V_j}(X_0+sI)=\lambda_{V_j}(X_0)+b_js,
\quad
\ell_{W_j}(X_0+sI)=\lambda_{W_j}(X_0)+d_js,
\]
where `a_j,b_j,d_j` are actual traces/evaluations at `I`. Equivalently, if matrices are written as `U_j=u_j+alpha_j I` with `u_j` traceless, then `a_j=3 alpha_j`.

The target has zero `I wedge Lambda^2(sl3)` antisymmetric component because `tr([B,C])=0`. Hence the trace parameters satisfy
\[
\Psi(a,b,d)=
\sum_j(a_jv_j\wedge w_j+b_jw_j\wedge u_j+d_ju_j\wedge v_j)=0.
\]
The trace-graded rank argument is valid when this equation forces all trace parameters to vanish. If all free orbits are traceless, comparing powers of `s` in the diagonal identity gives
\[
\operatorname{tr}(X_0^2)=\sum_i c_i\lambda_i(X_0)^2,
\qquad c_i=\ell_{L_i}(I),
\]
where the bilinear form is the trace form on `sl3` (the standard Killing form is a scalar multiple). Its Gram determinant in this investigation basis is `-3`, so its rank is 8. Each summand has rank at most one, so `f>=8`; with the earlier Cartan exterior-rank theorem `m>=4`, a pure cyclic rank-22 decomposition satisfying `ker Psi=0` must have `(f,m)=(10,4)`.

If every `P_j=<u_j,v_j,w_j>` is three-dimensional, the map from trace parameters to `Lambda^2(P_j)` is an isomorphism for each `j`, and `ker Psi=0` is equivalent to injectivity of the natural map
\[
\Phi:\bigoplus_j\Lambda^2(P_j)\to\Lambda^2(\mathfrak{sl}_3).
\]
For `m=4`, three-dimensionality of all four exterior summands follows from minimality of the Cartan trivector rank: a degenerate summand would express the Cartan trivector using at most three decomposable trivectors, which was excluded earlier. In degenerate `m>=5` configurations, `Phi` and `Psi` must not be conflated.

## Exact BILR component facts

[plane_invariant_extractor.py](../../quotient_cores/code/plane_invariant_extractor.py) writes [bilr_plane_invariants.json](../results/plane_invariants/bilr_plane_invariants.json), and [bilr_phi_minor.py](../code/bilr_phi_minor.py) writes the nonzero minor certificate [bilr_phi_rank12_minor.json](../results/plane_invariants/bilr_phi_rank12_minor.json) with determinant `-1`.

For the BILR rank-4 exterior configuration:

- the four trace-free planes all have dimension 3;
- `Phi` has rank 12, so `Psi` is injective and traces vanish for this four-plane configuration;
- internal recombination changes the ordered basis inside each plane but not the plane, while global adjoint applies one `PGL3` motion to all four planes; therefore the earlier 40/40 samples do not test other exterior components;
- all six pairwise intersections of the four planes have dimension 0, but this fact alone does not prove `Phi` injective because four-term bivector relations could still exist;
- each restricted determinant cubic is identically zero;
- each restricted trace quadratic is `2(xy+xz-yz)`, with matrix determinant `-2`;
- none of the four planes is closed under commutator;
- during development we also observed common left kernels `(1,0,0)`, `(1,-1,0)`, `(0,1,-1)`, `(0,0,1)`, a useful relative-position invariant to include in later component classification.

These facts are exact for the BILR four-plane configuration and its simultaneous `PGL3` orbit. They do not classify all rank-4 exterior decompositions of the Cartan trivector.

## Normalized trace-moment instrument

[moment_cubature_instrument.py](../../relaxations_and_cuts/code/moment_cubature_instrument.py) writes [moment_cubature_instrument.json](../../relaxations_and_cuts/results/moment_cubature/moment_cubature_instrument.json).

For active fixed cyclic cubes, allowing a possible scalar coefficient `rho_i`, set
\[
\mu_i=\lambda_i/c_i,
\qquad w_i=\rho_i c_i^3,
\qquad c_i=\ell_{L_i}(I)\ne0.
\]
In the BILR files `rho_i=1`. The first three trace moments in the traceless-free-orbit case become
\[
\sum_i w_i=3,
\qquad
\sum_i w_i\mu_i=0,
\qquad
\sum_i w_i\mu_i\otimes\mu_i=K,
\]
where `K(X,Y)=tr(XY)` on `sl3` in the basis `E01,E02,E10,E12,E20,E21,H0,H1`.

BILR is the exact integer positive control:

- 11 active nodes;
- weights `+1` for seven nodes and `-1` for four nodes;
- `sum w_i=3`, `sum w_i mu_i=0`, and `sum w_i mu_i mu_i^T=K` exactly;
- the 11 `mu_i` span rank 8 and have left kernel dimension 3;
- the weight vector lies in that left kernel;
- deleting any one BILR cube violates the moment equations. This is only a control for the fixed BILR nodes; it does not exclude moving ten-node configurations.

A useful exact consequence for `(10,4)` is that exactly eight active nodes are impossible. If eight active `mu_i` satisfy the quadratic moment, they must form a basis of `sl3^*`; the linear moment would then be a nontrivial relation among a basis with all weights nonzero. Thus a `(10,4)` solution under the traceless-free-orbit hypothesis has either nine or ten active nodes. Cubes with `c_i=0` are invisible to these first three trace moments but still appear in the degree-zero cubic equation; cubes proportional to `I` have `lambda_i=0` and affect only the scalar trace moment, so they should be treated separately in a complete enumeration.

[nine_node_reflection_cubature.py](../../quotient_cores/code/nine_node_reflection_cubature.py) supplies an explicit rational 9-node certificate for the first three moment equations with weights `(1^6,-1^3)`, using a rational reflection isometry. It writes [nine_node_reflection_cubature.json](../../relaxations_and_cuts/results/moment_cubature/nine_node_reflection_cubature.json), where `sum_weights=3`, the linear moment is zero, the quadratic moment is `K`, and the node matrix has rank 8. The older simple congruence search in `moment_cubature_instrument.json` has `constructed:false`; that only records the failure of that search path, not a nonexistence statement.

## Cubic residual control

[cubic_residual_control.py](../../quotient_cores/code/cubic_residual_control.py) writes [cubic_residual_control.json](../../relaxations_and_cuts/results/moment_cubature/cubic_residual_control.json).

Using the cyclic diagonal convention implemented by the BILR reconstruction, it verifies over `Z` that
\[
\operatorname{tr}(X_0^3)-3\sum_{j=1}^4
\lambda_{U_j}(X_0)\lambda_{V_j}(X_0)\lambda_{W_j}(X_0)
=
\sum_{i=1}^{11} w_i\mu_i(X_0)^3
\]
for the BILR configuration. The residual has 15 nonzero degree-3 coefficients in the chosen basis. For other rank-4 exterior configurations the residual cubic changes; this file is a BILR control, not a universal residual polynomial.

## Nontraceless branch for `m>=5`

[nontraceless_branch_checks.py](../../quotient_cores/code/nontraceless_branch_checks.py) writes [nontraceless_branch_algebra.json](../../relaxations_and_cuts/results/moment_cubature/nontraceless_branch_algebra.json).

Without tracelessness, the `s^1` equation is
\[
\operatorname{tr}(X_0^2)=\sum_i c_i\lambda_i^2+
\sum_j q_j,
\quad
q_j=a_j\lambda_{V_j}\lambda_{W_j}
+b_j\lambda_{W_j}\lambda_{U_j}
+d_j\lambda_{U_j}\lambda_{V_j}.
\]
In formal independent coordinates `(lambda_U,lambda_V,lambda_W)`, twice the symmetric matrix of `q_j` is
\[
\begin{pmatrix}
0&d&b\\ d&0&a\\ b&a&0
\end{pmatrix},
\qquad \det=2abd.
\]
Therefore, when the three restricted linear forms are independent, a nonzero single-orbit contribution has rank 2 or 3, never rank 1. After pullback to `sl3`, degenerate triples can have lower rank; for example if `w=u` and only `b` is nonzero, then `q_j=b lambda_u^2` has rank 1.

There is also a dependent-traceless-part branch. If `w=u+v`, then `u wedge v wedge w=0`; the orbit adds no Cartan volume. The mixed-trace relation is satisfied by `d=a+b`, leaving a two-parameter set of nonzero trace values, and the resulting quadratic is generically rank 2 (example `a=1,b=2`: `2 U^2 + 6 U V + V^2`). This shows that `(7,5),(4,6),(1,7)` cannot be closed by the analysis rank argument alone. They need an exact analysis of decomposable-bivector relations together with
\[
\sum_i c_i^2\lambda_i+
\sum_j(a_jb_j\lambda_{W_j}+a_jd_j\lambda_{V_j}+b_jd_j\lambda_{U_j})=0,
\]
\[
\sum_i c_i^3+3\sum_j a_jb_jd_j=3.
\]

## Research consequence

The current cyclic line has the following reliable structure:

1. pure cyclic characteristic-zero rank 22 has `m>=4` by the Cartan exterior-rank result;
2. if the mixed-trace trace-parameter map is injective, the trace grading gives `m<=4`, hence `(10,4)`;
3. on the BILR rank-4 exterior configuration, that injectivity holds exactly;
4. the `(10,4)` problem is now a PGL3-equivariant system coupling rank-4 exterior plane data to the normalized moment equations and the residual cubic, with nine or ten active fixed-cube nodes.

The next useful work is exact rank-4 exterior component classification and moment/cubic elimination, not random Koszul rank sweeping. If the work returns to `m>=5`, it must keep the nonzero-trace equations and dependent-orbit branches explicit.
