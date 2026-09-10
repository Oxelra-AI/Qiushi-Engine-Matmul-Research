# local projection membership and reduced Wang row set for the E11 distinct branch

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Scientific setting

The active finite-field object remains the distinct 19-point E11 quotient support problem over \(\mathbb F_2\). A support is a subset of the 255 nonzero quotient A-directions with cardinality 19 satisfying every E11-core Wang occupation row. A support that passes these rows is still only an A-support candidate; it must then pass the fixed-A B/C pipeline and exact tensor reconstruction.

This ARTIFACT corrects the analysis interpretation and runs the experiment that was actually needed: keep a complete fractional point of the full Wang LP, then ask whether selected 4-dimensional local color-count integer hulls separate its projections.

## Complete fractional LP point

Script: [fractional_local_membership.py](../../quotient_cores/code/fractional_local_membership.py)

Output: [global_fractional_solution.json](../results/local_hull/global_fractional_solution.json)

The LP solved is
\[
Ax\le 19-L,\qquad \sum_{p=1}^{255}x_p=19,\qquad 0\le x_p\le 1,
\]
with all 417,199 E11-core Wang rows. A full 255-coordinate floating-point solution was saved. In the stored run, the solution has 65 fractional coordinates and sum `19.000000000000004`. This is useful as a target for projection tests. It should not be described as a proof about all vertices or as a measured objective gap.

## Local 4-dimensional color projections of the fractional point

Scripts:
- [fractional_local_membership.py](../../quotient_cores/code/fractional_local_membership.py)
- [active_local_membership.py](../../quotient_cores/code/active_local_membership.py)
- [validate_local_membership.py](../../quotient_cores/code/validate_local_membership.py)
- [validate_active_membership.py](../../quotient_cores/code/validate_active_membership.py)

Outputs:
- [fractional_local_membership.json](../results/local_hull/fractional_local_membership.json)
- [membership_validation.json](../results/local_hull/membership_validation.json)
- [active_fractional_local_membership.json](../results/local_hull/active_fractional_local_membership.json)
- [active_membership_validation.json](../results/local_hull/active_membership_validation.json)

For a selected 4D dual color map \(\pi_F\), the local model has 16 integer color counts, total 19, fiber capacities 15 for the zero fiber and 16 for each nonzero fiber, and the 66 induced Wang rows from all nonzero subspaces of \(F\). The column-generation loop alternates between a restricted convex-combination master and an integer oracle for linear functionals on this 16-count model. A separation would give a valid pulled-back inequality only after the integer oracle closes the bound.

Two families of flags were tested:

1. Four 4D flags from pairs of dim-5 Wang-violating subspaces of the old 9-violation near-miss. All four projections of the saved global fractional LP point were expressed as convex combinations of feasible local integer profiles. Validation found zero failures. Reconstruction residuals were between about \(3.3\times10^{-15}\) and \(2.2\times10^{-14}\), and every profile in the displayed convex combinations satisfied the 66 local rows, total 19, and fiber capacities.

2. Eight 4D flags selected from pairs of active global LP rows of dimensions 5 or 6 with 4D primal intersections. All eight projections also had convex combinations of feasible local integer profiles. Validation found zero failures. Reconstruction residuals were at most about \(2.7\times10^{-14}\), with active combination sizes 12--14.

Scientific interpretation: these twelve selected local hulls do not cut this one numerical fractional point. This is a projection-specific result. It does not rule out other 4D flags, other fractional points, coupled projections, or finer color systems. The memberships are floating-point certificates; exact rational certificates were not constructed.

## Primitive-reduced Wang row set

Scripts:
- [primitive_reduced_wang.py](../../quotient_cores/code/primitive_reduced_wang.py)
- [reduction_spotcheck.py](../../quotient_cores/code/reduction_spotcheck.py)
- [reduced_wang_cpsat.py](../../quotient_cores/code/reduced_wang_cpsat.py)

Outputs:
- [primitive_reduced_wang_manifest.json](../../quotient_cores/results/reduced_wang/primitive_reduced_wang_manifest.json)
- `workspace/data/reduced_wang/primitive_reduced_rows.pkl`
- [primitive_reduction_spotcheck.json](../../quotient_cores/results/reduced_wang/primitive_reduction_spotcheck.json)
- [reduced_wang_cpsat_overlap_300s.json](../../quotient_cores/results/reduced_wang/reduced_wang_cpsat_overlap_300s.json)

The reduction recomputes the analysis local flag implication row-by-row:

- For dim-6 primal rows, the annihilator has dual dimension 2. If the zero-color upper bound is already forced by the three proper dual-point rows, the dim-6 row is dropped.
- For dim-5 primal rows, the annihilator has dual dimension 3. If the zero-color upper bound is already forced by all proper dual-point and dual-line rows, the dim-5 row is dropped.
- The implication is acyclic for the integer cardinality-19 occupation system: dropped dim-6 rows are forced by dim-7 rows, and dropped dim-5 rows are forced by dim-7 plus dim-6 rows; any dim-6 row used in that implication is either retained or itself forced by dim-7.

Counts from the manifest:

- Complete E11-core Wang rows: 417,199.
- Dropped dim-5/6 rows: 96,833.
- Retained rows: 320,366.
- Retained key hash: `604090dcf3a6ea0c9239cfe0a58fd6f32587bca1a632a65fbeb452f1d7793a67`.
- Dim-5 retained/dropped: 5,742 retained and 91,413 dropped.
- Dim-6 retained/dropped: 5,375 retained and 5,420 dropped.

An independent spot test recomputed the local maxima without importing the analysis helper and sampled 24 retained/dropped dim-5/6 decisions. It found zero failures: dropped rows had independent `max_n0 <= cap`, retained rows had independent `max_n0 > cap`.

A CP-SAT pilot using the reduced rows plus the 1,152 transported radius-3 overlap cuts added 320,364 explicit Wang inequalities: the complete-table dim-0 row is trivial and the dim-8 row is represented by the total cardinality equality. It returned `UNKNOWN` after about 269 s of solving; therefore it produced neither a Wang-admissible support nor an infeasibility proof. The run only shows that the reduced point-level model is buildable and can be used for future search.

## Consequence for the next work

The most reliable new information is that the tested single-flag integer hulls do not separate the stored fractional point, while the row-reduction gives a smaller equivalent integer occupation formulation for dim-5/6 implications. The next useful computation should either use the reduced row set in a genuinely cumulative support search, seek coupled multi-flag integer consequences, or search directly for a complete-Wang-admissible support and then send it to exact B/C completion. The present files do not solve the E11 core branch and do not change the global rank bounds.
