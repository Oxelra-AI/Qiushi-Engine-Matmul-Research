# exterior linear sections for the Cartan trivector

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Purpose

analysis failed before doing mathematics because Sage tried to write runtime state in a read-only location.  The useful correction is that the abelian one-orbit exterior ansatz needs no Groebner setup over a Pluecker ideal.

Let \(H\) be a finite abelian subgroup acting on \(\mathfrak{sl}_3\) by adjoint action and suppose the four exterior planes form one \(H\)-orbit.  For a plane volume \(p=U\wedge V\wedge W\in\Lambda^3\mathfrak{sl}_3\),
\[
  \sum_{h\in H} \Lambda^3(\operatorname{Ad}h)(s p)=\omega/3
\]
projects only to the \(H\)-invariant coordinates.  In an eigenbasis, the ansatz is therefore the linear section of \(G(3,8)\) given by proportionality of the invariant Pluecker coordinates of \(p\) and \(\omega/3\).  This is a way to find symmetric components of the rank-four exterior fiber; it cannot prove BILR uniqueness, because components with trivial stabilizer are invisible to all finite-symmetry ansaetze.

## New scripts and data

- [invariant_linear_section.py](../../quotient_cores/code/invariant_linear_section.py): exact modular construction of eigenbases, invariant Pluecker coordinates, linear-section equations, and initial chart reduction.
- [generate_singular_chart.py](../../quotient_cores/code/generate_singular_chart.py): emits direct Singular scripts for selected charts, including finite-field point equations and lex bases.
- [extract_f5_symmetry_points.py](../code/extract_f5_symmetry_points.py): extracts the 32 \(\mathbb F_5\) points from the lex bases for the selected `c4_regular` and `klein_diag` charts and computes plane-orbit geometry and \(\Phi\)-rank.
- [residual_koszul_symmetry_points.py](../code/residual_koszul_symmetry_points.py): tests a canonical internal frame for each extracted finite-field exterior point by the Koszul--Young rank of the residual cubic.
- [bilr_frame_calibration.py](../code/bilr_frame_calibration.py): identifies the BILR plane inside the extracted `c4_regular` chart and compares the canonical chart frame with the displayed BILR internal frame.
- [heisenberg_z3_fixed_orbits.py](../../quotient_cores/code/heisenberg_z3_fixed_orbits.py): records the cheap diagonal \(Z_3^2\) fixed-coordinate-plane obstruction.

Main outputs are under `workspace/data/exterior_linear_sections/`.

## Exact exterior-section results

### Regular \(C_4\) / BILR-type action

Over \(\mathbb F_5\) and \(\mathbb F_{13}\), `c4_regular` has adjoint character multiplicities
\[
  0,0,1,1,2,2,3,3,
\]
so \(\dim (\Lambda^3\mathfrak{sl}_3)^{C_4}=14\).  The target has no non-invariant coordinates.  The BILR first plane is a positive control: its invariant Pluecker coordinates are proportional to the target, with scale `4` over \(\mathbb F_5\) and `10` over \(\mathbb F_{13}\).

For the chart pivot `(0,2,7)`, direct Singular gives:

- over \(\mathbb F_5\): affine dimension `2`, projective degree `30`;
- over \(\mathbb F_{13}\): the same dimension and degree;
- with field equations over \(\mathbb F_5\): `vdim=32`, i.e. 32 rational points in that chart.

All 32 extracted \(\mathbb F_5\) points have four distinct three-dimensional planes, all pairwise intersections zero, and mixed-trace map rank \(12\).  Thus this tested BILR-type finite-field slice shows no \(\ker\Phi\) failure.

### Klein diagonal \(V_4\) action

The diagonal Klein family has character multiplicities two per character, again giving 14 invariant Pluecker coordinates.  The selected target-nonzero pivot `(2,5,6)` has:

- over \(\mathbb F_5\): affine dimension `2`, projective degree `12`;
- over \(\mathbb F_{13}\): the same dimension and degree;
- over characteristic zero, using a rational eigenbasis: affine dimension `2`, projective degree `12`.

With field equations over \(\mathbb F_5\) this chart also has 32 rational points.  All extracted points have four distinct three-dimensional planes, all pairwise intersections zero, and mixed-trace map rank \(12\).  This is evidence for a characteristic-zero \(V_4\)-symmetric rank-four exterior family.  It is not yet known whether it is \(PGL_3\)-conjugate to the BILR family or an inequivalent exterior component; comparing component invariants is a valuable next task.

### Split \(C_4\) with eigenspaces \(2+1\)

For `c4_2plus1`, the adjoint weights have multiplicities `0:4, 1:2, 3:2`, giving 20 invariant coordinates.  In target-nonzero charts tested over \(\mathbb F_5\) and \(\mathbb F_{13}\), the system becomes inconsistent after the linear substitutions; direct Singular with field equations returns the unit ideal.  This is only a checked chart-family failure, not a classification theorem.

### Diagonal \(Z_3^2\) fixed-coordinate planes

The diagonal \(Z_3^2\) fixed-coordinate computation has 8 invariant coordinate trivectors.  The Cartan target has six nonzero independent invariant coordinates among them, so four fixed coordinate planes cannot sum to \(\omega\).  This does not exclude the `1+3` pattern or non-coordinate invariant planes.

## Residual-cubic calibration: exterior planes do not determine the residual

For each extracted \(\mathbb F_5\) exterior point I also formed a residual cubic using the canonical chart basis, scaling one basis vector so that the exterior sum has the required normalization.  The Koszul--Young ranks were:

- `c4_regular`: ranks `1040, 1046, 1049, 1050`, eight points at each rank;
- `klein_diag`: rank `916` for all 32 points.

These ranks are all greater than 700, so these *particular canonical internal frames* do not give a rank-\(\le 10\) residual over \(\mathbb F_5\).  However this must not be over-read.  The calibration file `bilr_plane_vs_internal_frame_calibration.json` identifies the BILR first plane inside the extracted `c4_regular` chart (solution index 21).  For the same exterior plane:

- the canonical chart-frame residual has KY rank `1049` over \(\mathbb F_5\);
- the displayed BILR internal frame residual has KY rank `722` over \(\mathbb F_5\), matching the known 11-cube residual.

Thus the exterior fiber and the internal determinant-one frame search are separate problems.  Linear-section computations can find or parameterize rank-four exterior components and test \(\Phi\)-injectivity, but the rank-\(\le 10\) residual question still requires the internal-frame Strassen/Pfaffian/commuting-Hessian system or an explicit ten-cube reconstruction.

## Current scientific meaning

analysis replaces the failed Sage attempt with a working exact modular/Singular instrument.  It confirms the cheap invariant-coordinate formulation, recovers the expected BILR-type `C4` component, and finds a plausible characteristic-zero `V4`-symmetric exterior family of the Cartan trivector with \(\Phi\)-rank 12 in the tested chart.  No rank-22 matrix multiplication algorithm and no global rank-23 lower bound follow from this.  The useful next work is:

1. Compare the `klein_diag` exterior family with the BILR exterior family under \(PGL_3\): plane determinant cubics, trace conics, pairwise configurations, stabilizer action, and if necessary a direct conjugacy solve.
2. For either exterior family, attack the internal-frame residual problem with the witness-carrying condition: look for \(\ell,\lambda\) such that \(R-\lambda\ell^3\) has commuting normalized Hessian slices, which would produce nine simultaneous eigenforms plus the tenth form.  Use KY rank \(\ge701\) mod good primes as a certificate in the other direction, and treat any rank drop as a reconstruction signal.
3. Keep finite-field and symmetry scope explicit: these computations only see exterior components with nontrivial stabilizer and do not classify the unrestricted rank-one-span incidence for arbitrary rank-22 decompositions.
