# plan: bounded conic-guided integer pair-count pilot

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Scientific object

The unresolved finite-field object remains the distinct projected-A branch of the E11 quotient core. A 19-point support among the 255 nonzero quotient directions that satisfies all complete Wang rows would become an A-support candidate for fixed-A/B/C completion. A complete exclusion of all such supports, together with the already verified repeated-direction exclusion and E11 bridge, would raise the full-tensor lower bound over `F2`.

This plan tests one intermediate object for a fixed point-orbit count vector:

\[
\mathcal P_n^{(2)}=\{m\in\mathbb Z^{97}: E(n,m)=0,\ L(n,m)\le 0,\ M(n,m)\succeq0\},
\]

where `E,L` include the full analysis linear conditions and `M` is the 256 x 256 orbit-averaged moment matrix reduced by the analysis group-algebra blocks. A member of this set is not a support, but it gives a concrete profile for point-level graph/color realization. A certified empty result for a count vector deletes that branch from the support search.

## Start branch

Use

`n = [0,0,3,5,4,7]`.

Reasons:

- analysis found a numerical continuous witness under Wang RLT + triangle/Fortet + deterministic block totals + PSD.
- analysis found four exact integer pair-count assignments satisfying the full linear rows, but all were strongly non-PSD.
- The continuous witness has highly nonintegral `m_j=|P_j|y_j`, with max distance to an integer close to 0.5.
- The first two point orbits have zero count; this forces incident pair counts to zero and should allow useful face reduction.

Expected block totals for the nonzero orbit blocks are: diagonal `C(3,2)=3`, `C(5,2)=10`, `C(4,2)=6`, `C(7,2)=21`; off-diagonal totals `15,12,21,20,35,28`, summing with diagonals to 171.

## Required linear conditions

Retain the full analysis formulation, not the analysis reduced one:

1. analysis Wang RLT equality rows and upper-bound rows.
2. All 5,913 analysis triangle/Fortet rows.
3. Pair-cardinality equations.
4. Deterministic block-pair totals for the fixed `n`.
5. Bounds `0 <= m_j <= |P_j|`, with stronger zero bounds for pair orbits incident to zero point-orbit counts.
6. Any exact square cuts from analysis may be added as optional global cuts, but they cannot replace the PSD constraints.

Pure point rows must be checked as constants after fixing `n`; do not silently drop them when no pair coefficient appears.

## Face reduction before conic solving

The fixed-count moment matrix has known kernels

\[
u_a=(-n_a,1_{O_a}),\qquad M u_a=0.
\]

For `n_a=0`, PSD also forces all rows/columns in that orbit to vanish. Therefore the fixed-count SDP has no strict interior in the unreduced 256-dimensional space. Before using CLARABEL statuses for branching decisions:

1. Remove point coordinates in zero-count orbits and set all incident pair-count variables to zero.
2. Enforce block totals and remove pair variables whose block target is zero.
3. Remove or ignore the completely fixed trivial block associated with `(1,1_{O_a})` count fluctuations.
4. Project every analysis PSD block onto the orthogonal complement of known kernel directions inside that block, or at minimum score PSD margin only on nontrivial eigenvalues after full-matrix reconstruction.
5. Validate the reduction by comparing full labelled eigenvalues and block eigenvalues on analysis saved continuous witnesses and on the known non-PSD integer assignments.

Without this reduction, `optimal_inaccurate`, tiny negative eigenvalues, and CLARABEL failures may reflect degeneracy rather than mathematical obstruction.

## Bounded pilot algorithm

A practical pilot can be hybrid: CP-SAT carries exact integer linear constraints and square cuts; block SDP supplies guidance.

1. Build infrastructure from existing scripts:
   - `rlt_pair_lift.py` for stabilizer, point orbits, pair orbits, and Wang RLT;
   - `rlt_triangle_integrality.py` for triangle/Fortet rows and exact row checking;
   - `block_sdp_v2.py` for block coefficient matrices;
   - `fixed_count_block_psd.py` for fixed-count continuous SDP formulation;
   - `fixed_n_integer_pair_psd_loop.py` for exact integer-pair CP-SAT baseline.
2. Fix `n=[0,0,3,5,4,7]` and build the exact integer CP-SAT model with the full linear rows.
3. Solve a reduced continuous block SDP with variables `m_j` (or `y_j=m_j/|P_j|` with explicit normalization) and objective
   \[
   \max t\quad M_b(m)\succeq tI
   \]
   on the reduced PSD blocks. This gives a central fractional point and active blocks.
4. Branch on pair-count variables whose implied `m_j` is far from an integer and whose block sensitivity is high. For active reduced eigenvector `u`, score variable `j` by
   \[
   |m_j-\operatorname{round}(m_j)|\cdot |u^T(B_j/|P_j|)u|,
   \]
   aggregated over active blocks.
5. At each node, rerun the reduced continuous SDP under the current pair-count bounds/fixings. Numerical infeasible nodes may guide search but are not mathematical proof unless backed by exact data.
6. When CP-SAT returns an integer `m`, build the full labelled `M(n,m)` and test PSD. If non-PSD, derive an exact rational square cut and add it to the model. If PSD, save the profile as a target for realization.

## Exact artifacts required

For an integer PSD pair-count witness:

- fixed `n` and length-97 integer `m`;
- exact checks of all analysis equality and inequality rows;
- exact block totals;
- full `1152*M(n,m)` as an integer/rational matrix;
- an exact PSD certificate for the full matrix or reduced blocks (e.g. rational LDL/congruence, or another independently checkable certificate);
- hashes/metadata for orbit tables and Wang LUT.

For a branch exclusion:

- the exact integer model used;
- all square cuts with the generating vector `v`, reduced/gcd-normalized coefficients `(A,B,C)`, and the symbolic identity `C + A*n + B*m = 1152 v^T M(n,m)v`;
- a proof-producing PB/SAT certificate, or a complete branch tree whose leaves are closed by exact inequalities.

For a numerical-only pilot result:

- node counts, depths, bounds/fixings, SDP statuses, reduced PSD margins, integrality distances, and exact checks of every integer candidate;
- explicit labels that numerical conic statuses are search evidence only.

## Implementation traps to avoid

- Do not repeat analysis's omission of triangle/Fortet rows.
- Do not treat `optimal_inaccurate` or CLARABEL infeasibility as proof.
- Do not use full-matrix `lambda_min` as a convergence/branch score without removing known kernels.
- Keep `m_j` and `y_j=m_j/|P_j|` coordinates separate. In PSD blocks, coefficients on `m_j` are `B_j/|P_j|`; in block totals with `m` coordinates, coefficients are 1.
- Save the generating vector `v` for every exact square cut; analysis saved coefficients but not enough data to independently verify the rank-one PSD origin of each cut.
- Reduce square-cut coefficients by gcd and track maximum expression magnitude to avoid poor CP-SAT propagation or integer overflow.
- Use exact no-good constraints if needed; the analysis fallback placeholder did not correctly exclude a full vector.

## How this advances the tensor-rank goal

The pilot is worth one bounded construction/execution ARTIFACT because it uses a genuinely new capability: the analysis block SDP inside the integer pair-count search rather than after arbitrary CP-SAT vertices. If it finds a PSD integer profile, the next research action is point-level realization with fixed pair orbit counts and all complete Wang rows. If it produces a small exact contradiction for the branch, the direct 255-variable support search gets a real count deletion. If it only produces numerical ambiguity, we learn that the route is not yet converting conic structure into discrete evidence and can redirect effort toward support search or completion-aware constraints without pretending the moment route was impossible.
