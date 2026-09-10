# Symmetry quotient route after Terracini dimension compensation

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Research purpose

The active goal remains the exact tensor rank of \(T_{\langle3,3,3\rangle}\): find an exact rank-22 algorithm, or prove rank 23 optimal in a clearly specified algebraic setting.  analysis showed that first-order Terracini dimension counting is saturated by the matrix-multiplication stabilizer: a hypothetical rank-22 decomposition of \(T_{333}\) would have 24 additional infinitesimal kernel directions from the \(GL_3^3\) sandwich stabilizer, exactly compensating the expected first-order dimension.  This ARTIFACT turns that insight into a more precise research route: quotient the full-span shortened incidence by term scalings and stabilizer directions, rather than applying blind second-order computations to the unsliced equations.

## Corrected mathematical state

Let \(r=22\).  Write
\[
X=[u_i\otimes v_i]_{i=1}^{22}\in K^{81\times 22},\qquad T=T_{333}.
\]
If the decomposition is minimal, then \(X\) has full column rank: any nontrivial relation among the columns lets one absorb one \(w_i\) into the others and shorten the expression.  Full factor spans \(\langle u_i\rangle=\langle v_i\rangle=\langle w_i\rangle=K^9\) are also forced by the three flattening ranks of \(T_{333}\).

On a full-UV-rank chart choose 22 rows \(R\) such that \(M=X_R\) is invertible.  Then
\[
W=M^{-1}T_R,
\]
and the shortened equations are
\[
F_R(U,V)=T_{\bar R}-X_{\bar R}M^{-1}T_R=0,
\]
531 equations in 396 \((U,V)\)-variables, with \(\det M\ne0\).  This is the exact chart object from earlier analysis.

In the shortened \((U,V)\)-variables the gauge tangent has dimensions
\[
\dim H_{\rm scale}=44,
\quad \dim H_{\rm stab}=26,
\quad \dim(H_{\rm scale}\cap H_{\rm stab})=d\ge2,
\]
so the actual gauge dimension is \(70-d\) and the quotient variable dimension is
\[
396-(70-d)=326+d.
\]
The transverse layer is \(d=2\), giving a 68-dimensional gauge and a 328-dimensional quotient chart.  The analysis statement “forced rank drop exactly 24” should therefore be read precisely as: in the transverse full-span full-UV layer, stabilizer symmetry forces a rank drop of at least 24 from the generic shortened Jacobian rank 352, so at a smooth rank-22 point one expects \(\operatorname{rank}DF_R=328\).  If \(d>2\) or if the decomposition has additional deformations, the rank can be lower and belongs to a separate stratum.

The stabilizer action is algebraic over characteristic zero.  In trace notation,
\[
\dot X=AX-XB,
\quad \dot Y=BY-YC,
\quad \dot Z=CZ-ZA,
\]
and cyclicity of trace gives \(\dot T=0\).  The one-dimensional common scalar kernel in \(\mathfrak{gl}_3^3\) leaves an effective 26-dimensional stabilizer action.

## Computation 1: local gauge-slice pilot

Script:

- [gauge_quotient_pilot.py](../../quotient_cores/code/gauge_quotient_pilot.py)

Output:

- [gauge_quotient_pilot.json](../../quotient_cores/results/gauge_quotient/gauge_quotient_pilot.json)

Modular field: \(\mathbb F_{65521}\).

Main checked numbers:

- Random full-span rank-22 controls: shortened Jacobian rank 352; term-scaling + coordinate slice already gives full augmented rank 396; the combined formal gauge matrix has rank 68 and intersection \(d=2\).  These random tensors are **not** \(T_{333}\), so the matrix-multiplication stabilizer directions are not kernel directions there; this control verifies only the coordinate-slice linear algebra and generic transversality of the gauge columns.
- `cn122` rank-23 control: shortened Jacobian rank 320; combined gauge rank 70 with \(d=2\); the augmented matrix has rank 390 in 414 variables, leaving exactly 24 post-gauge first-order directions.  Direct follow-up check: `SJ @ scale = 0` and `SJ @ stab = 0` over \(\mathbb F_{65521}\), so these are genuine kernel directions at a \(T_{333}\) decomposition.
- Natural 27-term decomposition: stabilizer--scaling intersection \(d=8\), hence it is a concrete nontransverse, termwise-aligned control and explains why the \(d=2\) layer cannot be the whole problem.

Consequence: a local coordinate slice can remove the 68 transverse gauge directions near a reference solution.  It is not a global finite moving frame.  The gauge constants, nonzero conditions, and finite chart coverage still have to be constructed before using it for a rigorous global exclusion.

## Computation 2: projected Segre--MinRank kernel model

review proposed a useful equivalent formulation.  Let
\[
L=\operatorname{im}(T_{333}:K^9_W{}^*\to K^9_U\otimes K^9_V),\quad \dim L=9,
\]
and choose \(\pi:E=K^9\otimes K^9\to E/L\), \(\dim E/L=72\).  Existence of \(W\) with \(T=XW\) is exactly
\[
L\subseteq \operatorname{span}\{x_1,\ldots,x_r\},\qquad x_i=u_i\otimes v_i.
\]
For full column rank \(X\), this is equivalent to
\[
\operatorname{rank}(\pi X)=r-9.
\]
For \(r=22\) this means rank 13.  On a 13-column chart,
\[
(\pi X)_J=(\pi X)_I C,
\quad C\in K^{13\times9},
\]
which gives 648 sparse cubic equations.  Unlike the 531 Schur equations, this representation has more variables but low degree and a sparse quotient basis.

Script:

- [projected_kernel_model.py](../../quotient_cores/code/projected_kernel_model.py)

Output:

- [projected_kernel_model.json](../../quotient_cores/results/projected_kernel_model/projected_kernel_model.json)

For \(T_{333}\), I constructed a very sparse quotient \(\pi\): 54 coordinate rows outside the 27 UV support rows, plus 18 pairwise differences among the three support UV rows in each W-slice.  The matrix has shape \(72\times81\), rank 72, annihilates \(T_{uv}\), and row weights 1 or 2.

Calibration:

- Random rank-22 tensor controls: \(\operatorname{rank}(\pi X)=13\) and the chart residual is zero.
- Random full-rank \(U,V\) against fixed \(T_{333}\): \(\operatorname{rank}(\pi X)=22\), with all 531 Schur residual entries nonzero in the selected chart.
- `cn122` rank-23: \(\operatorname{rank}(\pi X)=14=r-9\), chart residual zero.
- Every one-term truncation of `cn122` and `serendipitous_8d34`: \(X\) has rank 22 but \(\operatorname{rank}(\pi X)=14>13\), so the projected kernel rank condition already excludes those direct deletions, matching the previous first-order/nonlinear deletion failures in a cleaner way.

Variable counts for the sparse cubic model after term projectivization and stabilizer quotient are
\[
16r+9(r-9)-24.
\]
For \(r=22\), this is \(352+117-24=445\); for \(r=21\), 420; for \(r=20\), 395.  Thus lower-UV-rank 22-term representations should not be handled as a singular 22-term chart; they compress to shorter minimal decompositions and belong to the corresponding \(r\le21\) kernel models.

## Computation 3: semisimple termwise-aligned pilot

If the stabilizer--scaling intersection has dimension \(d>2\), then some noncentral stabilizer element acts on each summand by termwise scalars.  In the semisimple case, after diagonalizing \(P,Q,R\), the three factor spaces decompose into weight spaces
\[
A_\alpha=\operatorname{span}\{E_{ab}:p_a-q_b=\alpha\},
\]
\[
B_\beta=\operatorname{span}\{E_{bc}:q_b-r_c=\beta\},
\]
\[
C_\gamma=\operatorname{span}\{E_{ac}:r_c-p_a=\gamma\}.
\]
The tensor splits into blocks \(T_{\alpha\beta\gamma}\) with \(\alpha+\beta+\gamma=0\).  A termwise-aligned decomposition splits over these blocks; hence the sum over blocks of any block lower bound is a valid lower bound for that aligned stratum.  No tensor-rank direct-sum conjecture is being used, because the given aligned decomposition itself is weight-separated.

Script:

- [semisimple_weight_blocks.py](../../deformation_and_incidence/code/semisimple_weight_blocks.py)

Output:

- [weight_block_pilot.json](../../deformation_and_incidence/results/semisimple_weight_blocks/weight_block_pilot.json)

Pilot enumeration over sorted eigenvalue triples in \(\{0,1,2,3,4\}\) tested 42,750 noncentral patterns and found flattening-lower-bound sums with histogram:

- 18: 1,500 patterns
- 21: 6,000 patterns
- 22: 600 patterns
- 23: 7,400 patterns
- 27: 27,250 patterns

There are 58 distinct block signatures in this box.  Thus many semisimple repeated-difference patterns are excluded by flattening sums \(\ge23\), but many hard repeated-difference patterns survive the first flattening test with lower bounds 18, 21, or 22.  The generic distinct-difference case has 27 one-dimensional coordinate blocks and therefore needs 27 coordinate summands; the hard part is repeated-difference semisimple flats.

Important correction: the analysis single Jordan-block example is not a complete proof of the nonsemisimple layer.  A general lemma is needed: if the difference operators have enough eigenvectors to support full-span termwise alignment, then their nilpotent parts must vanish in the relevant coupled differences.  This should be proved or tested before declaring the whole nonsemisimple aligned layer impossible.

## review corrections and useful route advice

review independently confirmed the main usefulness of the 328-dimensional transverse quotient, but corrected several points:

1. The coordinate-slice script gives only an infinitesimal slice near a reference point.  It does not construct a global algebraic moving frame or prove finite chart coverage.  It must not be used as a global rank-23 proof object without moving-frame charts and open conditions.
2. For gauge dimension, use \(70-d\), not always 68.  The transverse layer has \(d=2\).  Nontransverse layers with \(d>2\) are exactly where semisimple/Jordan alignment matters.
3. Random rank-22 controls verify generic rank and slice mechanics, not the existence of a \(T_{333}\) solution with rank 328 after quotient.
4. The stabilizer directions are right-kernel directions of the parameter map, not explicit left conormal covectors.  If conormal equations are needed, compute \(\ker J^T\) directly.
5. A finite-field point search can find seeds and support Hensel lifting, but absence of \(\mathbb F_p\)-rational points is not a characteristic-zero lower bound.  Algebraic-closure emptiness and characteristic-zero transfer require Gröbner/Nullstellensatz-style certificates or rational reconstruction of exact objects.
6. The lower-UV-rank 22-term layer is better replaced by shorter \(r\le21\) minimal models, since a minimal expression has all two-factor pairings independent.

## Updated route judgment

The characteristic-zero route is still scientifically stronger than merely completing an \(\mathbb F_2\) increment, because it addresses the original problem over characteristic zero/rational fields and turns the dimension compensation into a usable algebraic representation.  However, the current computation has not found a rank-22 seed or a lower-bound certificate.  The best immediate route is to build reusable exact algebraic machinery for the transverse quotient and the aligned strata, while continuing to watch related analysis for finite-field proof objects or full-LUT supports.

The concrete next mathematical/computational objects are:

1. **Moving-frame gauge charts** for the transverse full-span full-UV layer.  Start with finite projective term normalizations and a simple stabilizer frame based on two or three anchor linear combinations of \(U\) and \(V\); record the determinant open conditions and prove what open set is covered.  Coordinate slices are fine for local search/Hensel lifting, but global exclusion needs these finite charts.
2. **Sparse cubic kernel model implementation** that can generate a polynomial system for a fixed 13-term pivot chart, with finite term-normalization charts.  It should support modular Groebner/F4 or numerical-to-exact root search, and each candidate must be verified by recovering \(W\) and checking all 729 Brent equations.
3. **cn122 quotient Kuranishi system** in the post-gauge 24 variables.  This is not a direct rank-22 proof, but it is a small exact testbed: choose 320 independent shortened residuals plus 70 gauge equations, solve formally for 390 variables in terms of 24, compute the quadratic map into the remaining 211 residuals, and look for term disappearance or pairing-rank-decrease branches.
4. **Exact semisimple flat enumeration** beyond the small-box pilot.  Enumerate difference-equality flats up to \(S_3^3\) symmetries, compute block flattening bounds, and for surviving lb \(\le22\) blocks run exact small tensor-rank checks or derive stronger block-specific obstructions.
5. **Finite-field verification**: continue verifying DRAT leaves and range-branch semantics, but keep the logical scope as \(\mathbb F_2\) only unless a valid transfer argument or exact characteristic-zero construction appears.

## What this ARTIFACT establishes

This ARTIFACT establishes a corrected and executable algebraic direction, not a final result:

- The 328-dimensional quotient is valid only for the transverse full-span full-UV layer.
- The projected kernel model gives an equivalent low-degree formulation of the full-UV rank-22 condition and cleanly explains the 531 equations.
- Known rank-23 truncations fail the projected rank condition \(\operatorname{rank}(\pi X)=13\).
- Nontransverse aligned strata are now a finite-style weight-block problem; first flattening bounds exclude many but not all repeated-difference patterns.
- No rank-22 decomposition, characteristic-zero rank-23 lower bound, or complete \(\mathbb F_2\) rank-23 theorem has been obtained.
