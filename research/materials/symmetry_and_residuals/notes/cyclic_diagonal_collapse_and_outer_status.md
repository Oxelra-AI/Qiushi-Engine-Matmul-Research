# cyclic outer symmetry — F2 diagonal collapse and quotient status

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Research position

The active structured family is the pure cyclic outer De Groote ansatz for a cyclic-invariant rank decomposition of \(T_{\langle 3,3,3\rangle}\). A rank-22 cyclic skeleton has
\[
  f+3m=22,
\]
where \(f\) projectively fixed terms are cubes and \(m\) free terms occur in 3-cycles under factor rotation. This is only a symmetry stratum; it does not cover the general full-independent-UV incidence.

analysis built full cyclic F2 SAT encodings but they timed out for the key rank-22 skeletons. analysis used the diagonal specialization \(A=B=C=M\) to remove the cube variables from the high-degree Boolean ANF.

## Diagonal collapse over \(\mathbb F_2\)

Let \(x_{ab}\) be the nine Boolean coordinates of \(M\). In the Boolean ANF ring over \(\mathbb F_2\), every linear form satisfies
\[
  \ell(M)^3 = \ell(M)
\]
as a function on \(\mathbb F_2^9\). Hence every fixed cyclic cube contributes only a linear form to the diagonal specialization. A free 3-orbit contributes
\[
\ell_U\ell_V\ell_W + \ell_V\ell_W\ell_U + \ell_W\ell_U\ell_V
= 3\ell_U\ell_V\ell_W
= \ell_U\ell_V\ell_W.
\]
Therefore any cyclic F2 decomposition with \(m\) free orbits must satisfy the orbit-only high-degree condition
\[
  H\!\left(\sum_{j=1}^m \ell_{U_j}\ell_{V_j}\ell_{W_j}\right)
  = H(\operatorname{tr}(M^3)),
\]
where \(H\) takes the degree 2 and degree 3 parts of the Boolean ANF.

The computed ANF of \(\operatorname{tr}(M^3)\) has exactly three linear terms, no quadratic terms, and eight cubic terms:
\[
(x_{00},x_{11},x_{22}) \text{ in degree 1},\qquad
\{013,026,134,156,237,268,457,578\}\text{ in degree 3}
\]
using flattened indices \(0=00,1=01,2=02,3=10,4=11,5=12,6=20,7=21,8=22\). Thus the necessary condition has
\[
  \binom{9}{2}+\binom{9}{3}=36+84=120
\]
Boolean equations in \(27m\) orbit variables.

## Certified F2 exclusion from the diagonal collapse

Script: [f2_diagonal_collapse.py](../../quotient_cores/code/f2_diagonal_collapse.py)  
Results: [diagonal_collapse_results.json](../../quotient_cores/results/diagonal_collapse/diagonal_collapse_results.json)

With Kissat and DRAT replay, the 120-equation diagonal condition gives:

| free orbits \(m\) | result | proof status |
|---:|---|---|
| 0 | UNSAT | DRAT verified |
| 1 | UNSAT | DRAT verified |
| 2 | UNSAT | DRAT verified |
| 3 | UNSAT | DRAT verified |
| 4 | SAT | witness saved separately |
| 5 | SAT | witness saved separately |
| 6 | SAT | witness saved separately |
| 7 | SAT | witness saved separately |

The proof files are under `workspace/data/diagonal_collapse/diag_highdeg_m*.drat`; the largest used proof is `diag_highdeg_m3.drat` (about 24 MB, verified by `drat-trim`).

Conclusion over \(\mathbb F_2\): no cyclic decomposition with \(m\le3\) free cyclic 3-orbits can exist. For rank 22 this excludes the high-fixed skeletons
\[
  (f,m)=(22,0),(19,1),(16,2),(13,3).
\]
This is a necessary-condition exclusion, but because every complete cyclic decomposition would satisfy the condition, the exclusion is rigorous for those skeletons over \(\mathbb F_2\).

A stricter check using only the 84 cubic/quotient equations is also UNSAT for \(m=0,1,2,3\) and SAT for \(m=4\):
[deg3_only_results.json](../../quotient_cores/results/diagonal_collapse/deg3_only_results.json). Thus the exterior/quotient part alone already forces at least four free cyclic orbits over \(\mathbb F_2\); the 36 quadratic diagonal equations are not needed for the \(m\le3\) exclusion.

SAT witnesses for diagonal survival at \(m=4,5,6,7\) were extracted and directly rechecked against all 120 high-degree ANF equations:
[diagonal_collapse_sat_witnesses_m4_m7.json](../../quotient_cores/results/diagonal_collapse/diagonal_collapse_sat_witnesses_m4_m7.json).
These witnesses are not tensor decompositions; they only show the diagonal necessary condition stops excluding once \(m\ge4\).

## review verification and a terminology correction

review verified the derivation and encoding in
`independent-verification-record`.

Important correction from review: over \(\mathbb F_2\), the 165-dimensional coefficient subspace fixed by the full \(S_3\) action is not the same as the linear span of actual Boolean cubes \(u^{\otimes 3}\); the latter has dimension 129. analysis's phrase "Sym^3 quotient" meant the coefficient-symmetric quotient of cyclic-invariant tensors. analysis's full 120-dimensional diagonal high-degree projection is better described directly as the degree-2/3 Boolean ANF projection. This distinction does not affect the \(m\le3\) UNSAT proof.

The within-orbit \(S_3\) lexicographic symmetry breaking in the diagonal-collapse script is safe only for the diagonal product \(\ell_U\ell_V\ell_W\), where \(U,V,W\) are interchangeable. It should not be copied into the full cyclic Brent encoding, which generally has only cyclic symmetry within each 3-orbit.

## Attempts on surviving F2 skeletons

The cube-selector/decoding-style full cyclic encoding was built in
[orbit_cube_decode_sat.py](../code/orbit_cube_decode_sat.py). It uses 511 cube-selector variables with an at-most-\(f\) counter and native XOR cyclic equations. It was validated by fixing the known elementary rank-27 cyclic decomposition in `positive_rank27_m8_f3_fixed_units.cnf`, which CryptoMiniSat accepts immediately; without fixing variables, even this positive instance can be hard for the solver.

Runs:

- `(f,m)=(10,4)`: `orbit_cube_m4_f10.cnf`, 9111 variables, 21292 regular clauses, 369 XOR clauses; CryptoMiniSat timed out at 600 s.
- `(f,m)=(1,7)`: `orbit_cube_m7_f1.cnf`, 7149 variables, 20149 regular clauses, 369 XOR clauses; CryptoMiniSat timed out at 600 s.
- a specialized `(1,7)` encoding using only nine cube variables rather than 511 selectors ([f1_eliminated_cyclic.py](../code/f1_eliminated_cyclic.py)) also timed out at 600 s.
- scanning eight fixed cube choices for `(1,7)` ([fixed_cube_orbit_scan.py](../code/fixed_cube_orbit_scan.py)) gave timeouts for each 60 s subproblem; fixed-cube splitting alone is not enough.

These timeouts are not mathematical evidence for impossibility; they only show the surviving full cyclic F2 skeletons need a stronger representation.

## Characteristic-zero quotient direction

The 84-dimensional cyclic quotient by coefficient-symmetric tensors is naturally \(\Lambda^3 K^9\). A free cyclic orbit maps to a decomposable 3-vector \(U\wedge V\wedge W\), and fixed cube terms vanish. The quotient of \(T_{333}\) is, up to scalar, the Cartan-type 3-form
\[
  \omega(X,Y,Z)=\operatorname{tr}(X[Y,Z])
\]
on \(\mathfrak{gl}_3\), equivalently the alternating part of \(\operatorname{tr}(ABC)\). In the standard matrix-entry basis, the nonzero exterior terms are
\[
(001,010,100), (000,002,200), (001,010,111), (001,012,200),
(002,010,210), (002,200,222), (111,012,210), (012,210,222)
\]
with signs as recorded in [exterior_flattening_ranks.json](../results/exterior_flattening/exterior_flattening_ranks.json).

I computed standard wedge flattening ranks for this 3-form in [exterior_flattening.py](../code/exterior_flattening.py). The strongest lower bound from these flattenings is only exterior rank \(\ge3\), not \(>3\): for example the \(\Lambda^3 V\to\Lambda^6 V\) wedge map has rank 56, while a single decomposable term contributes at most \(\binom{6}{3}=20\), giving only \(\lceil 56/20\rceil=3\). Thus simple exterior flattenings do not reproduce the F2 \(m\le3\) exclusion in characteristic zero. A stronger invariant or explicit secant-variety/elimination argument is needed.

## Related Mathematical Checks

The k=7 nonadjacent-matching Wang graph certificates were independently checked by replaying one clique-cover certificate and one graph-IS DRAT proof:

- `verify_graph_certificate.py` verifies the idx033 clique cover: 82 survivors, target 13, color count 10, and 354 intra-color pairs checked against residual-1 Wang rows.
- `drat-trim` verifies idx035 graph independent-set CNF: 3135 variables, 25518 clauses, VERIFIED in about 4 s.

## Current mathematical state after analysis

New reliable result: over \(\mathbb F_2\), cyclic rank-22 decompositions with \(m\le3\) free 3-orbits are excluded with replayed DRAT certificates. The remaining cyclic F2 rank-22 skeletons are
\[
  (f,m)=(10,4),(7,5),(4,6),(1,7).
\]
No rank-22 decomposition was found, and no global rank-23 lower bound was proved.

The strongest next work is no longer generic Gröbner or longer unstructured SAT. It is to build a better exact representation for the four surviving cyclic F2 skeletons, preferably exploiting the split into:
1. the 84 exterior quotient equations for \(m\) decomposable 3-vectors,
2. the 36 quadratic diagonal equations and other non-diagonal cyclic equations,
3. the actual 129-dimensional span of Boolean cubes with a syndrome-decoding/cardinality layer.

In characteristic zero, the quotient problem becomes the exterior rank/secant problem for the Cartan 3-form on \(\mathfrak{gl}_3\). Closing \(m\le3\) there would require a stronger equation than the basic wedge flattenings; this is a suitable construction/proof task rather than another long CDCL run.
