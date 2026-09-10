# Wang-F2 support execution summary

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

Active goal remains the exact rank of the 3x3 matrix multiplication tensor.  This note concerns only the finite-field Wang occupation support route toward excluding length-20 decompositions over F2.  It is not a rank-22 algorithm, not a characteristic-zero lower bound, and not a completed proof of `R_F2(T_<3,3,3>) >= 21`.

## Matching branch update

A delivered fair-seed solve from analysis closed one additional anchored matching stratum:

- `k=5`, matching `idx15`, fixed prefix `[1,16,27,256,438]`.
- Evidence: [summary.json](../../quotient_cores/results/fair_seed/k5_idx15_copy/summary.json).
- The copied analysis seed CNF `workspace/data/matching/k5_batch/idx015/round025.cnf` was bound to base metadata and learned JSONL with exact regeneration: 189,188 clauses, 7,765 variables, 160,090 learned clauses checked, no base or learned provenance errors.
- CaDiCaL solved the seed CNF UNSAT in 772.94 s; the proof-producing rerun took 791.9 s and `drat-trim` verified in about 1641.0 s.  DRAT SHA256: `246b24fd5ee9f57c4d8e2a193cdfb9b97af4059bc3d39a3790f626774044ca53`.

Updated matching ledger: [progress-52704e8d92.json](../../quotient_cores/results/progress/progress-52704e8d92.json) records 15/38 fixed matching strata closed:

- k=7: all six strata closed;
- k=6: idx22,23,24,25,28 closed;
- k=5: idx12,13,14,15 closed;
- all k=1,2,3,4 and k=5 idx16-21, k=6 idx26,27,29-31 remain open.

Fair regenerated seed solves that did **not** close:

- k6 idx27: [summary.json](../../quotient_cores/results/fair_seed/k6_idx27_regen/summary.json), exact regenerated 119,232-clause CNF, SAT in 1.51 s, returned support has 10,487 full-LUT violations.
- k2 idx1: [summary.json](../../quotient_cores/results/fair_seed/k2_idx01_regen/summary.json), exact regenerated 347,365-clause CNF, SAT in 1.51 s, returned support has 9,473 full-LUT violations.

## Rep2 adjacent-pair marked-orbit execution

analysis profiled the rep2 adjacent-pair branch by fixing `[1,2]` and marking a third selected point by one of 17 orbits under `Stab([1,2])`.  analysis obtained the first certified marked-orbit exclusion:

### Closed marked orbit: prefix `[1,2,3]`

- Orbit representative: 3, rank 1, orbit size 1 in [summary.json](../../quotient_cores/results/rep2_marked_profile/summary.json).
- Seed witness run: [summary.json](../../quotient_cores/results/rep2_marked_witness/rep003/summary.json) ended MAX_ROUNDS after 20 rounds, 64,933 learned clauses, 73,799 clauses.  Local strict regeneration/provenance verification: [strict_verification.json](../../quotient_cores/results/rep2_marked_witness/rep003/strict_verification.json).
- Fair seed solve: [summary.json](../../quotient_cores/results/fair_seed/rep2_rep003_witness20/summary.json) was SAT in 1.48 s with 749 complete-LUT violations, so the seed itself was not already contradictory.
- Low-residual promotion run: [summary.json](../../quotient_cores/results/rep2_rep003_promotion/lowres_12w8/summary.json) promoted 80 complete Wang rows (all residual 2), adding 3,135 clauses and reaching UNSAT at wave 10.  CaDiCaL proof-producing rerun took 3.97 s and `drat-trim` verified in 3.17 s.
- Independent strict promotion verifier: [strict_verification.json](../../quotient_cores/results/rep2_rep003_promotion/lowres_12w8/strict_verification.json) confirms exact CNF regeneration, 60 fresh/disjoint auxiliary intervals beyond seed top 4182, zero promotion provenance problems, and DRAT replay verified.

Interpretation: this excludes every Wang-admissible rank-20 A-support in the adjacent-pair branch whose third marked selected point lies in the orbit of point 3, after normalizing the adjacent pair to `[1,2]`.  It closes 1 of the 17 marked rep2 orbit branches.  It does **not** close rep2.

### Nonclosing marked-prefix tests

The same 20-round witness seed + 12-wave low-residual promotion pattern was tested on four other marked orbit representatives:

- rep10 (rank 2, orbit size 12): witness seed [summary.json](../../quotient_cores/results/rep2_marked_witness/rep010/summary.json) exact-verified and fair-solve SAT with 2,272 violations; promotion [summary.json](../../quotient_cores/results/rep2_marked_promotion/rep010_lowres_12w8/summary.json) ended MAX_WAVES after 96 promotions, 2,395 extra clauses, final SAT model with 2,433 full-LUT violations.  Strict promotion verification passed.
- rep12 (rank 2, orbit size 24): witness seed exact-verified and fair-solve SAT with 4,307 violations; promotion [summary.json](../../quotient_cores/results/rep2_marked_promotion/rep012_lowres_12w8/summary.json) ended MAX_WAVES after 96 promotions, 2,233 extra clauses, final SAT model with 1,101 violations.  Strict promotion verification passed.
- rep80 (rank 2, orbit size 24): witness seed exact-verified and fair-solve SAT with 1,012 violations; promotion [summary.json](../../quotient_cores/results/rep2_marked_promotion/rep080_lowres_12w8/summary.json) ended MAX_WAVES after 96 promotions, 3,995 extra clauses, final SAT model with 2,208 violations.  Strict promotion verification passed.
- rep225 (rank 3, orbit size 48): witness seed exact-verified and fair-solve SAT with 2,029 violations; promotion [summary.json](../../quotient_cores/results/rep2_marked_promotion/rep225_lowres_12w8/summary.json) ended MAX_WAVES after 96 promotions, 2,345 extra clauses, final SAT model with 1,791 violations.  Strict promotion verification passed.

These nonclosing runs are valid formulas and useful branch evidence, but they are not exclusions.

## Failed residual-layer profile

[fixed_prefix_residual_profile.py](../../quotient_cores/code/fixed_prefix_residual_profile.py) was created to estimate complete residual-layer encoding sizes for arbitrary fixed prefixes.  The first version assumed the wrong `process_rep2` return shape and was repaired.  The repaired unoptimized scan over prefixes `[1,2,3]`, `[1,2,10]`, `[1,2,12]` timed out at 300 s and produced no profile artifact.  Do not reuse its absence as evidence about residual-layer feasibility; the script needs optimization or a narrowed scan.

## Next scientific execution

The most valuable finite-field work is now:

1. Continue proof-producing closure of remaining matching strata; fair seed solves can uncover hidden UNSAT seeds, as in k5 idx13 and idx15, but several seeds are genuinely SAT relaxations.
2. Continue rep2 by marked-orbit subbranches.  The first orbit `[1,2,3]` is closed; 16 marked orbits remain.  Existing nonclosed seeds for reps 10,12,80,225 should be treated as reusable exact formulas, not as failures of the branch method.
3. Improve the residual-layer profiling or a row-selection representation before launching blanket long runs, because only one of five tested marked orbits closed under the current simple low-residual selector.
4. Preserve exact row provenance, seed regeneration, auxiliary interval checks, and DRAT replay for every counted branch closure.

## Addendum: additional rank-1 marked rep2 tests in analysis

After the first version of this note, two more rank-1 marked orbit representatives were tested:

- rep4 (rank 1, orbit size 4): witness seed [summary.json](../../quotient_cores/results/rep2_marked_witness/rep004/summary.json) ended MAX_ROUNDS after 20 rounds and 81,432 learned clauses; strict seed verification passed; fair seed solve [summary.json](../../quotient_cores/results/fair_seed/rep2_rep004_witness20/summary.json) was SAT with 5,545 full-LUT violations; low-residual promotion [summary.json](../../quotient_cores/results/rep2_marked_promotion/rep004_lowres_12w8/summary.json) ended MAX_WAVES after 96 promotions and 2,998 promotion clauses; strict promotion verification passed, but no exclusion was obtained.
- rep8 (rank 1, orbit size 12): witness seed [summary.json](../../quotient_cores/results/rep2_marked_witness/rep008/summary.json) ended MAX_ROUNDS after 20 rounds and 58,381 learned clauses; strict seed verification passed; fair seed solve [summary.json](../../quotient_cores/results/fair_seed/rep2_rep008_witness20/summary.json) was SAT with 904 full-LUT violations; low-residual promotion [summary.json](../../quotient_cores/results/rep2_marked_promotion/rep008_lowres_12w8/summary.json) ended MAX_WAVES after 96 promotions and 6,270 promotion clauses; strict promotion verification passed, but no exclusion was obtained.

The machine-readable updated marked-orbit status is [summary.json](../../quotient_cores/results/rep2_marked_status/summary.json): 7 marked orbits were tested in analysis, and only rep3 is closed.  Thus rank-1 marked rep2 subbranches are not uniformly easy; the rep3 singleton closure should not be generalized without proof.

## Final analysis rep2 marked-orbit status correction

review verifier `independent-verification-record` independently read the rep003 proof artifacts and agrees that, conditional on the Wang LUT, prefix normalization, and encoding semantics, the proof object supports the local exclusion of 20 distinct projective A-point supports containing `[1,2,3]`.  It also flags essential wording discipline: this is not an exclusion of all rank-20 decompositions, not a closure of rep2, not a support-count fraction, and the phrase `1/17 marked orbits` is only branch bookkeeping because a support may contain possible third marked points in several orbits.  The strict verifier is independent replay at the artifact level, not a completely independent implementation of the whole LUT and encoding stack.

analysis then completed the seed/fair-solve/promotion comparison for all five rank-1 third-point orbits of `Stab([1,2])`: reps 3,4,8,24,32.  Only the singleton orbit rep3 closed.  Reps 4,8,24,32 all have exact witness seeds, fair seed SAT results, and verified promoted formulas ending MAX_WAVES, so rank-1 marked subbranches are not uniformly easy.  Additional tested non-rank-1 reps 10,12,80,225 also remain open under the same bounded promotion pattern.  The updated status file [summary.json](../../quotient_cores/results/rep2_marked_status/summary.json) records 9 tested marked orbit representatives, with only rep3 closed and orbit-size bookkeeping 1/509; this denominator is point-orbit coverage, not support coverage.
