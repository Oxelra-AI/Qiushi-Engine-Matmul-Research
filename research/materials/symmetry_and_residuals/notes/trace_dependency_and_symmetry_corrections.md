# corrected trace-dependency family restrictions and whole-support symmetry discipline

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Why the analysis handoff had to be repaired

The six classes in [orbit_structure.json](../../quotient_cores/results/family_consequence/orbit_structure.json) are orbits of **individual** nonzero E11 quotient directions. They are not orbits of 19-point supports. Wang rows, contraction guards, trace guards, and B/C compatibility depend on incidences between all selected points and many subspaces/functionals; those incidences are lost if one replaces the 255 variables by six orbit counts. Similarly, canonicalization cannot be done independently in each point orbit: a single element of the E11 stabilizer must act on the whole support. Any future symmetry use must therefore keep the point variables and use whole-support lexicographic constraints or a genuine stabilizer chain.

The analysis parity wording also needed repair. For a trace-certificate guard set `G`, each selected direction `p` must be classified into three distinct cases using only the trace functionals with `q(p)=1`:

1. **locally inconsistent:** the hitting trace functionals have an odd dependency, so the equations `phi_q(X)=1` already imply `0=1` for any term with direction `p` under that saturation pattern;
2. **forced:** the local system is consistent and the certificate tensor functional `F(p)` lies in the span of available hitting trace functionals, so its value is fixed;
3. **free:** the local system is consistent but `F(p)` is not in that span, so the certificate parity cannot be turned into a pure support row unless no such direction is selected or explicit evaluation variables are retained.

Thus the ten-contraction parity row from analysis is sound only under its guard and when the support contains no selected free or locally inconsistent direction. It is not valid as an unconditional row over all supports satisfying the ten saturations.

## Sound trace-dependency cut

Let `H` be an odd dependency among corrected rank-9 trace functionals:
\[
\sum_{q\in H}\phi_q=0,\qquad |H|\equiv 1\pmod 2.
\]
If a selected direction `p` is hit by every `q\in H`, and all contractions in `H` are saturated (`w(q)=9`), then the local equations would impose `phi_q(X_p)=1` for all `q\in H`, and summing gives `0=1`. Therefore any valid support-level relaxation must satisfy
\[
 x_p=1 \Longrightarrow \exists q\in H: w(q)\ne 9.
\]
In the distinct E11-core branch we already impose `w(q)\ge 9` for rank-9 contractions, so this becomes the linear necessary cut
\[
\sum_{q\in H}(w(q)-9) \ge x_p.
\]
This cut is a genuine B/C trace-compatibility restriction. It is not a complete rank-one completion condition and cannot by itself prove a tensor-rank lower bound.

## Extraction results

Scripts and files:

- [trace_dependency_family.py](../../quotient_cores/code/trace_dependency_family.py)
- [trace_dependency_cut_analysis.json](../../quotient_cores/results/trace_dependency_cuts/trace_dependency_cut_analysis.json)
- [trace_dependency_cuts.json](../../quotient_cores/results/trace_dependency_cuts/trace_dependency_cuts.json)
- [trace_dependency_size5.py](../../quotient_cores/code/trace_dependency_size5.py)
- [trace_dependency_size5_summary.json](../../quotient_cores/results/trace_dependency_cuts/trace_dependency_size5_summary.json)
- `workspace/data/trace_dependency_cuts/trace_dependency_size5_cuts.pkl`
- [trace_certificate_cuts.py](../../finite_certification/code/trace_certificate_cuts.py)
- [trace_certificate_family_cuts.json](../../finite_certification/results/trace_dependency_cuts/trace_certificate_family_cuts.json)

Global odd-dependency structure for all 72 corrected rank-9 trace functionals:

- there are 72 rank-9 contractions and their trace functionals span dimension 9;
- for 246 of 255 directions, the hitting rank-9 functionals have a shortest odd dependency of size 5;
- for exactly nine directions
  `5,6,7,33,34,35,37,38,39`, no odd dependency occurs in the full hitting set; these are the rank-deficient E11 cross directions from analysis;
- there are no size-3 odd dependencies;
- enumerating all size-5 dependencies gives 216,576 local cuts across 246 directions.

On the 31 stored near-miss supports from analysis, the complete saturated-pattern local inconsistency test rejects 7 supports. The enumerated size-5 cuts reject the same 7 supports, with 23 term-level violations. The best analysis 12-Wang-violation near-miss has **no** local odd-dependency violation; its corrected trace contradiction remains a multi-contraction certificate/parity phenomenon rather than a single-term local inconsistency.

## Corrected certificate-family classification

`trace_certificate_cuts.py` rebuilt certificates for 15 stored trace-inconsistent supports and classified all 255 directions for each certificate. The primary analysis near-miss certificate now has the correct classification:

- guard contractions: 10;
- locally inconsistent directions: 9;
- forced directions: 102 (`56` forced value 0, `46` forced value 1);
- free directions: 144.

The near-miss itself selects 19 forced directions, so the pure parity row is applicable to that particular support and gives forced sum 0 versus tensor RHS 1. This explains the local contradiction without making the row unconditional. Other certificates range from no free directions to many free directions. The original analysis cross-application statistic did not check the target support's saturation guards, so the phrase that it hit all stored supports is withdrawn; the repaired guarded statistic is in [guarded_trace_certificate_coverage.json](../../finite_certification/results/neighborhood_repair/guarded_trace_certificate_coverage.json) and shows 15 guarded hits among 23 deduplicated stored targets. All such targets still have Wang violations, so this remains mechanism validation and search guidance rather than a global result.

## Search experiments using the repaired cuts

Scripts:

- [distinct_trace_cut_cpsat.py](../../quotient_cores/code/distinct_trace_cut_cpsat.py): 255-variable CP-SAT with threshold/full Wang rows, contraction weights, optional local odd-dependency cuts, and optional whole-support lex constraints (not yet used in the main run).
- [distinct_cert_trace_cpsat.py](../../quotient_cores/code/distinct_cert_trace_cpsat.py): adds correctly guarded certificate local-inconsistency and parity cuts.
- [cert_trace_separator.py](../../quotient_cores/code/cert_trace_separator.py): adaptive exact Wang-row separator starting from `L>=15` Wang rows plus trace-certificate cuts.
- [evaluate_trace_supports.py](../../occupation_and_completion/code/evaluate_trace_supports.py): exact rescanning and corrected trace evaluation for new supports.

Key outputs:

1. Baseline `L>=15` without trace cuts (`cpsat_L15_no_trace_60s.json`) remained `UNKNOWN` after a short 60 s solve; this run is too short to compare directly with analysis but confirms the rebuilt model is large.
2. `L>=15` plus only the 246 minimal local cuts (`cpsat_L15_mintrace_120s.json`) still returns the old 12-violation near-miss. This is expected because that support has no local odd-dependency violation.
3. `L>=15` plus 15 corrected certificate-cut packages (`cpsat_L15_certcuts_180s.json`) finds a new support
   `[1,2,3,4,8,20,24,31,32,36,64,73,127,128,141,160,182,192,219]`
   with only 9 complete Wang violations, all `L=12`; it passes zero-domain, linear membership, transversality, and size-2 quotient-rank checks. Corrected compressed and full trace systems both reject it (`sat9=12`, compressed rows 280, variables 228, trace-functional rank 8, certificate row count 10; full trace rows 756, variables 1539, certificate rows 32). This is a better near-miss and a useful positive target for future row/certificate extraction, but it is not Wang-admissible.
4. Adaptive separator `separator_L15_certcuts_6r_180s.json` added exact violated Wang rows. Round 0 found an 18-violation support with transversality and quotient-rank failures; round 1 found a different 18-violation support with no transversality or size-2 quotient-rank failure and corrected trace consistency; round 2 returned `UNKNOWN` after 172.9 s. Thus the repaired cuts changed the search landscape and improved one direct candidate, but did not solve the distinct branch.

## Scientific state after analysis

The distinct E11 core branch remains open. No complete-Wang-admissible 19-point support, no rank-19 E11 core decomposition, no rank-22 full algorithm, and no proof of `R_F2(T)>=21` was obtained. The useful advance is methodological: corrected trace dependencies now yield sound family restrictions and correctly guarded certificate cuts, and the six point-orbit classification is preserved only as structural information or as a basis for whole-support symmetry, not as a six-count model.

The strongest immediate continuation is to use the new 9-violation trace-inconsistent support as a target for extracting additional compact corrected certificates and Wang rows, then feed those into adaptive separation. Whole-support symmetry constraints may be added, but only after validating that the lex encoding preserves known candidates under a single stabilizer element and does not independently canonicalize point orbits.

## Addendum after augmented-certificate separator and exact trace evaluation

After adding the certificate extracted from the first 9-violation trace-inconsistent support, the augmented certificate library contains 17 certificates in [trace_certificate_family_cuts_augmented.json](../../finite_certification/results/trace_dependency_cuts/trace_certificate_family_cuts_augmented.json). A new separator run using these 17 packages is [separator_L15_augcertcuts_4r_240s.json](../../quotient_cores/results/trace_dependency_cuts/separator_L15_augcertcuts_4r_240s.json). It found, before timing out on the next round, a different 9-violation support

`[1,2,3,4,8,20,24,31,32,36,64,73,109,127,128,141,160,182,219]`.

This support has exactly nine complete Wang violations, all `L=12`, and passes the currently implemented zero-domain, linear-membership, transversality, size-2 quotient-rank, local odd-dependency, compressed corrected-trace, and full corrected-trace tests. Its evaluation is in [aug_separator_support_trace_evaluation.json](../../occupation_and_completion/results/trace_dependency_cuts/aug_separator_support_trace_evaluation.json). It is still not a valid A-support because of the nine full-Wang violations, but it is now the best near-miss under the repaired independent-verification-record model and a useful target for future exact row separation or certificate extraction. The previous 9-violation support from `cpsat_L15_certcuts_180s.json` is trace-inconsistent and supplied one of the two augmented certificates.
