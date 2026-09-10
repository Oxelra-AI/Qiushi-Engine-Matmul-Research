# linked annihilator-weight representation for the distinct E11 core

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Setting

After the repeated projected-A direction branch was certified impossible for the E11 quotient core over `F2`, the live core problem is a length-19 support with 19 distinct nonzero projected A-directions.  The complete Wang table gives, for every subspace `U <= F2^8`,

\[
  \operatorname{occ}(U)=\sum_{p\in U\setminus\{0\}}x_p \le 19-L(U).
\]

For a dual vector `q`, define the linked contraction weight

\[
  w(q)=\sum_{p:\langle q,p\rangle=1}x_p.
\]

If `D=U^perp` has dimension `k`, then each point outside `U` is hit by exactly `2^(k-1)` nonzero functionals in `D`, while points in `U` are hit by none.  Hence

\[
  \sum_{q\in D\setminus\{0\}} w(q)=2^{k-1}(19-\operatorname{occ}(U)),
\]

and the Wang row is exactly

\[
  \sum_{q\in D\setminus\{0\}} w(q)\ge 2^{k-1}L(U).
\]

The exactness depends on tying every `w(q)` to the same Boolean support variables.  Freely chosen integer weights would lose the geometry.

## Files produced

- Script: [hybrid_annihilator_core.py](../code/hybrid_annihilator_core.py).
- Identity and near-miss analysis: [analysis_L15_support.json](../results/hybrid_annihilator/analysis_L15_support.json).
- Direct-vs-hybrid comparison: [direct_L14_120s_with_L15_hint.json](../../quotient_cores/results/direct_compare/direct_L14_120s_with_L15_hint.json) and [hybrid_L14_360s.json](../results/hybrid_annihilator/hybrid_L14_360s.json).
- Full `L>=12` hybrid run: [hybrid_L12_1200s.json](../results/hybrid_annihilator/hybrid_L12_1200s.json).
- Dual residual profile: [dual_residual_profile.py](../../quotient_cores/code/dual_residual_profile.py), output [dual_residual_profile_L15_support.json](../../occupation_and_completion/results/dual_residual_profile/dual_residual_profile_L15_support.json).
- Adaptive hybrid separator: [hybrid_violation_separator.py](../../quotient_cores/code/hybrid_violation_separator.py), output [hybrid_separator_L14_4r_180s.json](../../quotient_cores/results/hybrid_separator/hybrid_separator_L14_4r_180s.json).
- Dual orbit profile and orbit-augmented run: [dual_violation_orbits.py](../../quotient_cores/code/dual_violation_orbits.py), [dual_violation_orbits.json](../results/hybrid_annihilator/dual_violation_orbits.json), [hybrid_orbit_augmented.py](../../quotient_cores/code/hybrid_orbit_augmented.py), and [orbit_augmented_L14_300s.json](../../quotient_cores/results/hybrid_orbit_augmented/orbit_augmented_L14_300s.json).
- Repaired arbitrary fixed-A completion interface in [fixed_A_rankone_solver.py](../../occupation_and_completion/code/fixed_A_rankone_solver.py); single-support completion output [L15_12violation_single_completion_300s.json](../../occupation_and_completion/results/completion/L15_12violation_single_completion_300s.json); batch output [distinct_candidate_completion_repaired.json](../../occupation_and_completion/results/completion/distinct_candidate_completion_repaired.json).

## Exact identity check

`analysis_L15_support.json` verifies the annihilator identity over all 417,199 E11-core rows with zero failures.  For all table dimensions, the term counts match the expected dual compression:

- dim 5 rows: direct support row has 31 point variables; dual form has 7 weights.
- dim 6 rows: direct support row has 63 point variables; dual form has 3 weights.
- dim 7 rows: direct support row has 127 point variables; dual form has 1 weight, exactly the individual contraction lower-bound row.

A complete threshold `L>=12` hybrid encoding keeps 255 Boolean support variables, introduces 255 linked weight variables, encodes 408,201 Wang rows, and reduces linear terms from 6,981,081 direct point appearances to 4,396,281 combined appearances.  Across all nontrivial rows the same representation would reduce 7,448,805 direct point appearances to 4,437,255 combined appearances.

## Current 12-violation support in dual language

The analysis `L>=15` support

`[1,2,3,4,8,20,24,31,32,64,73,109,127,128,141,160,182,192,219]`

has 12 complete-Wang violations, all with `L=12` and excess one.  The dual-weight form explains them as joint contraction-weight shortages:

- Six dim-6 rows have dual `k=2`; each requires a three-weight sum at least 24 and the support gives 22.  Their weight pattern is one `w=4` plus two `w=9`, and their contraction-rank pattern is one rank-3 and two rank-9 contractions.  Individual lower bounds only force `3+9+9=21`, so the Wang row adds three units beyond individual contraction bounds.
- Six dim-5 rows have dual `k=3`; each requires a seven-weight sum at least 48 and the support gives 44.  Four rows have rank pattern `3,3,3,6,6,9,9`; two rows have rank pattern `3,3,3,6,6,6,6`.  These add nine or fifteen units beyond the sum of individual contraction lower bounds.

The twelve rows are not explained by zero-domain, linear membership, saturated transversality, or tested size-2 quotient-rank cuts: all those tests pass for this support.  Their obstruction is a simultaneous pencil/dual-subspace occupancy requirement rather than a failure of single contraction ranks.

## Dual orbit structure

Under the contragredient action induced by the standard E11 stabilizer on the quotient core, the twelve violating annihilator subspaces meet three orbits:

- One dual-line orbit of size 288 contains all six dim-6 violations.
- One dual-plane orbit of size 288 contains four dim-5 violations.
- One dual-plane orbit of size 72 contains two dim-5 violations.

Four of the six dual planes each contain one of the six violating dual lines; the other two violating dual planes contain none of those six lines.  Adding the three full orbits to the `L>=14` hybrid model inserts 648 new `L=12` rows.  The resulting CP-SAT run returned `UNKNOWN` after 301.355 seconds, so the orbit families are structurally real but not yet a closed proof-producing subsystem.

## Solver comparison

With the best known hint:

- Direct `L>=14` representation: 338,839 Wang rows, 4,804,875 direct point appearances, CP-SAT `OPTIMAL` in 37.941 s, returning the same 12-violation support.
- Hybrid `L>=14` representation: 338,839 Wang rows, 299,683 direct rows plus 39,156 annihilator rows, 3,858,219 total linear appearances after adding 255 weights, CP-SAT `OPTIMAL` in 31.939 s, returning the same support with zero weight-link mismatches.

Without a hint, both direct and hybrid `L>=14` models returned `UNKNOWN` in short runs; the hybrid used less wall time before stopping (137.694 s for the 180 s budget versus 181.309 s), but this is not mathematical evidence.  The full `L>=12` hybrid run returned `UNKNOWN` after 1201.408 s; it did not find a complete-Wang support and did not prove nonexistence.

The adaptive separator beginning with `L>=14` found the same 12-violation support, added exactly those 12 rows in annihilator form, and then returned `UNKNOWN` after 139.839 s.  This shows that the missing rows are the immediate obstruction for the best known support, but it does not settle the complete distinct branch.

## Fixed-A completion repair and local B/C information

The previous arbitrary-support completion script was broken because `solve_fixed_A_completion` was missing.  I added a programmatic solver to [fixed_A_rankone_solver.py](../../occupation_and_completion/code/fixed_A_rankone_solver.py).  It computes saturated domains for an arbitrary fixed A multiset, stops immediately on zero-domain or linear impossibility, otherwise solves the rank-one B/C completion equations by CP-SAT XOR constraints and reconstructs any feasible terms.

This repaired interface found:

- The older analysis 15-violation support is fixed-A rank-one completion infeasible in 5.342 s.
- The analysis round-12 16-violation support is completion infeasible in 0.110 s.
- The analysis 12-violation support is completion infeasible in 146.483 s after passing zero-domain, linear membership, transversality, and size-2 quotient-rank tests.

These are local fixed-A facts.  Since each support still violates Wang occupation, no completion result can turn it into a rank-19 core construction.  The value is that the B/C solver now works for arbitrary supports and can be run immediately if a complete-Wang-admissible support appears.

## Current understanding

The annihilator representation is an exact reorganization of Wang occupation that makes the best near-miss scientifically clearer: the hard leftover rows are low-L but low dual-dimension joint contraction-weight inequalities.  Individual contraction lower bounds, saturated-domain tests, and tested quotient-rank cuts do not reach them.  The representation moderately reduces row size for high-dimensional subspaces and exposes three stabilizer orbits behind the twelve missing rows, but the tested hybrid and orbit-augmented CP-SAT models remain undecided.

The distinct E11-core branch is still open.  A complete-Wang-admissible length-19 distinct support has not been found, and no proof-producing exclusion exists.  The most useful continuation is to exploit the dual-subspace organization rather than add rows blindly: search for a compact family of dual-line/dual-plane joint weight inequalities that closes the complete distinct branch, or use the hybrid encoding to find a complete admissible support and then run the repaired exact B/C completion immediately.
