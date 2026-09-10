# Contraction-weight excess formulation enters the E11 support search

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

research: research_record. Field: F2. Object: 19-term distinct E11 quotient/core support for the 3x3 matrix multiplication tensor.

## Mathematical object encoded

For an 8-bit quotient direction `u` and a nonzero contraction mask `lambda`, activity is `<lambda,u>=1` over F2.  For a final selected 19-point support with variables `x_p`, define

\[
 m_\lambda=\sum_{p\ne0} x_p [\langle\lambda,p\rangle=1].
\]

For two contractions `lambda, mu`, F2 gives the exact identity

\[
 h_{\lambda\mu}=|I_\lambda\cap I_\mu| = (m_\lambda+m_\mu-m_{\lambda+\mu})/2,
\]

where `m_0=19`.  This avoids separate overlap variables.

The contraction matrix is still

\[
 M_\lambda=\Lambda^T\otimes I_3,
\]

with rank `r_lambda = 3 rank(Lambda)`.  The implementation checked the same nonzero lambda distribution as earlier: 33 rank-one, 150 rank-two, 72 rank-three.

For rank-one/rank-two targets `mu`, the model uses integer excess variables

\[
0\le e_B(\mu),e_C(\mu)\le 9-r_\mu,
\qquad e_B(\mu)+e_C(\mu)\le m_\mu-r_\mu.
\]

For a tight source `lambda` (`m_lambda=r_lambda`), the guarded leakage inequalities are encoded as

\[
2 e_B(\mu)\ge r_\lambda+m_\mu-m_{\lambda+\mu}-2\dim(U_\lambda\cap U_\mu),
\]

and the analogous row-space/C inequality.  The guard is final tightness, not a DFS-prefix condition.  Feasible excess variables remain only necessary A-level evidence and do not imply B/C completion.

Two CP-SAT encodings were implemented:

1. `contraction_weight_excess_search.py`: indicator boolean `tight_lambda` with implications `m_lambda=r_lambda` / `m_lambda>=r_lambda+1` and enforced leakage rows.
2. `excess_bigm_experiment.py`: a big-M formulation

\[
2e + K m_\lambda - m_\mu + m_{\lambda+\mu}\ge r_\lambda+K r_\lambda-2d
\]

where `K` is chosen so the inequality is vacuous when `m_lambda>=r_lambda+1`.  This removes 255 tightness booleans and tests whether propagation improves.

## Calibration and correction of analysis same-W interpretation

`eval_samew814.json` reclassified the 814 same-W deletion A-lists using all rank-one/rank-two/rank-three scalar contraction tests, not only rank-one/rank-two scalar tests.  The verified rank-21 pool still passes all conditions, and the known L15 and analysis near-supports still pass the contraction-weight excess necessary condition.

Among the 54 local same-W supports that had passed shadow consistency and coordinate-purity:

- 17 were scalar-clean if only rank-one/rank-two scalar contractions were checked.
- Only 1 remains scalar-clean after rank-three scalar contractions are included.
- 0 satisfy the full all-source contraction-weight excess condition.
- Only that single full-scalar-clean survivor is rejected by leakage without a scalar deficit.
- `samew_rank3_contribution.json` shows this single full-scalar-clean leakage rejection is already from rank-one/rank-two sources; rank-three tight sources did not create a new scalar-clean rejection in this local family.

This resolves the earlier ambiguity: most of the analysis “scalar-clean” local cases were not scalar-clean against the full contraction-rank baseline.  The same-W evidence still gives a useful local example of leakage beyond scalar counts, but much less broadly than analysis suggested, and it remains a local repeated-A near-miss family.

## Support-search experiments

Files:

- [contraction_weight_excess_search.py](../code/contraction_weight_excess_search.py)
- [excess_bigm_experiment.py](../../quotient_cores/code/excess_bigm_experiment.py)
- [samew_rank3_contribution.py](../../quotient_cores/code/samew_rank3_contribution.py)
- [eval_samew814.json](../results/contraction_weight_excess/eval_samew814.json)
- [samew_rank3_contribution.json](../results/contraction_weight_excess/samew_rank3_contribution.json)
- [solve_reduced_scalar90.json](../results/contraction_weight_excess/solve_reduced_scalar90.json)
- [solve_reduced_excess90.json](../results/contraction_weight_excess/solve_reduced_excess90.json)
- [bigm_scalar_excess20.json](../results/contraction_weight_excess/bigm_scalar_excess20.json)
- [bigm_reduced_excess90.json](../results/contraction_weight_excess/bigm_reduced_excess90.json)

Results:

- Reduced-Wang + full scalar baseline only, 90 s per solve: `UNKNOWN`.  Model: 511 variables; 320,364 retained Wang rows.
- Reduced-Wang + indicator-guarded excess, 90 s: `UNKNOWN`.  Model: 1,132 variables; 366 excess variables, 255 tight booleans, 46,482 B and 46,482 C leakage inequalities.
- Reduced-Wang + big-M excess, 90 s: `UNKNOWN`.  Model: 877 variables, no tightness booleans, same 46,482 B and 46,482 C leakage inequalities; solve time 69.6 s vs 91.5 s for indicator, still no support/candidate/proof result.
- Scalar-only without Wang found a 19-point support quickly, but its post-scan has 453 complete-Wang violations and 26 leakage violations; this is only a sanity check that the post-verifier detects weak A supports.
- Scalar + excess without Wang returned `UNKNOWN` at 20 s for both encodings, showing the excess constraints are nontrivial for CP-SAT even before Wang rows.

Longer complete-Wang tasks are running in the managed runtime:

- `s10_t22_tool1`: complete Wang + full scalar + contraction-weight excess, 600 s solver time, output [solve_complete_excess600.json](../results/contraction_weight_excess/solve_complete_excess600.json).
- `s10_t23_tool1`: complete Wang + full scalar baseline only, 600 s solver time, output [solve_complete_scalar600.json](../results/contraction_weight_excess/solve_complete_scalar600.json).

These tasks are experiments only.  `UNKNOWN` or non-proof `INFEASIBLE` must not be used as a tensor-rank theorem.

## Current scientific reading

The contraction-weight formulation is the right way to put the low-excess idea into the support search without preselecting supports.  It is coverage-preserving for distinct 19-point supports because all variables are the original support indicators and derived final contraction weights.  However, the first CP-SAT experiments did not yet produce a complete-Wang-compatible support or a solver proof of exclusion.  The big-M representation is somewhat smaller and faster than the indicator formulation, so it is the better basis for further solver engineering.

The rank-nine source caution is important.  Rank-three tight sources are valid leakage sources, but in the local same-W data they mainly interact with scalar-dirty supports; the only full-scalar-clean local leakage obstruction did not need a rank-three source.  The next valuable work is to use the big-M contraction-weight model as a support generator/checker under complete Wang or under a certified branch/orbit decomposition, and to connect any support survivors to shadow consistency and exact fixed-A B/C completion with proof objects.

## Additional source-rank comparison

After the main note, I also compared big-M excess runs using only rank-one/rank-two tight sources (`--source-ranks 12`) against the all-source run.  With no Wang rows and 20 s, source-ranks-12 still returned `UNKNOWN`; with reduced Wang and 90 s it also returned `UNKNOWN` after 91.397 s.  The source-12 model has 33,306 B and 33,306 C leakage inequalities, compared with 46,482+46,482 for all sources.  In this short CP-SAT comparison, fewer rank-three-source inequalities did not make the reduced-Wang problem easier; however the two runs used different seeds and no theorem follows.  This supports the caution: rank-three tight sources are valid but should be used because they are mathematically justified, not because their quantity is presumed to add independent exclusions.

Additional files:

- [bigm_scalar_excess_source12_20.json](../results/contraction_weight_excess/bigm_scalar_excess_source12_20.json)
- [bigm_reduced_excess_source12_90.json](../results/contraction_weight_excess/bigm_reduced_excess_source12_90.json)

## Complete-Wang 600 s runs delivered after analysis handoff

The managed tasks `s10_t22_tool1` and `s10_t23_tool1` both completed successfully at the process level and wrote their declared JSON outputs, but neither decided the support problem.

- [solve_complete_excess600.json](../results/contraction_weight_excess/solve_complete_excess600.json): complete Wang + full scalar + indicator-guarded all-source excess.  CP-SAT status `UNKNOWN`; build 17.902 s, solve 576.364 s, elapsed 594.821 s.  Model: 1,132 variables; 417,197 Wang rows added; 366 excess variables; 255 tight booleans; 46,482 B and 46,482 C leakage inequalities.  No candidate support and no proof object.
- [solve_complete_scalar600.json](../results/contraction_weight_excess/solve_complete_scalar600.json): complete Wang + full scalar baseline without excess.  CP-SAT status `UNKNOWN`; build 15.087 s, solve 601.865 s, elapsed 617.399 s.  Model: 511 variables; 417,197 Wang rows added.  No candidate support and no proof object.

The excess model used fewer conflicts/branches than the scalar baseline in this run but many LP iterations, so this is a search-behavior comparison rather than mathematical evidence.  Both outputs reinforce that direct complete-Wang CP-SAT, even with the contraction-weight excess layer, has not yet produced a support or an exclusion.
