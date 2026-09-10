# Singleton→Pair Hierarchy for Wang Branch Closure

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Method
For each fixed-E11 branch (rep2, rep16), we apply a systematic hierarchy:
1. **Singleton test**: For each HR orbit representative, test if a single HR point
   can appear in ANY Wang-admissible support at rank-1 count k. Uses the
   complete 8.28M-row Wang LUT compressed to ~30K unique rank-1 masks.
2. **Pair test**: Among surviving HR points, enumerate all canonical pair classes
   under the branch stabilizer. Test each pair as a relaxation.
3. **Closure**: If ALL pairs are infeasible, no triple exists → k is closed.
4. **Cross-k monotonicity**: Infeasible at k₀ ⟹ infeasible at k ≥ k₀.
   So pair/singleton exclusions accumulate across k levels.

## Rep16 Results

### k=17: CLOSED (CP-SAT level)
- Singleton test: 27/33 orbits INFEASIBLE → 378/444 HR points eliminated
- Surviving: 6 orbits, 66 HR points
  - Orbits: 19(2), 33(8), 37(8), 257(16), 266(16), 267(16)
- Exhaustive canonical pairs: 102 classes, ALL INFEASIBLE
- Combined with exact-k=18 (DRAT-verified): rep16 branch has k ≤ 16

### k=16: Running (153 canonical pair classes among 83 HR points)
- First 64 of 153 canonical pairs: ALL INFEASIBLE
- Surviving orbits: 19(2), 26(1), 33(8), 37(8), 98(16), 257(16), 266(16), 267(16)

### Singleton max viable k per orbit:
- orbit 17: max_viable_k = 1 (always excluded)
- orbits 160, 161: max_viable_k = 14
- orbits 20, 28, 34, 35, 38, 39, 84, 96, 100, 102, 164, 165, 228, 229,
  258, 259, 272, 273, 274, 275, 282, 283: max_viable_k = 15
- orbits 26, 98: max_viable_k = 16
- orbits 19, 33, 37, 257, 266, 267: max_viable_k ≥ 17

## Rep2 Results

### k=17: Running (~1000 canonical pair classes among 432 HR points)
- Singleton test: 3 orbits INFEASIBLE, 1 UNKNOWN → 30+ HR points eliminated
- Surviving: 14 orbits, 432 HR points (including orbit 17 as undetermined)
  - Orbits: 17(6), 25(6), 28(12), 33(24), 34(24), 35(24), 80(24), 84(24),
    96(48), 98(48), 160(48), 161(48), 224(48), 225(48)
- Preliminary: all 78 inter-orbit-rep pairs + ~50 intra-orbit pairs tested = ALL INFEASIBLE
- Full exhaustive test running

### Singleton max viable k per orbit:
- orbits 10, 12, 20: max_viable_k = 16 (orbit 17 UNKNOWN at k=17)
- orbits 25, 28, 33, 34, 35, 80, 84, 96, 98, 160, 161, 224, 225:
  max_viable_k ≥ 17

## Proof Status
- All results are CP-SAT computational evidence, not DRAT-certified.
- Each pair exclusion can be converted to a skeleton CNF (~478K vars).
  CaDiCaL solves them UNSAT in ~60s, but drat-trim verification
  has not completed in 1800s for the one tested case.
- A complete proof chain requires either:
  (a) DRAT certification for each singleton and pair exclusion, or
  (b) A single combined CNF for the entire k-level

## Rep10 Results (rank-2 second point)

### k=17: CLOSED BY SINGLETONS (!!!)
- General oracle adapted for rank-2 second points: fixed_rank1=[E11],
  fixed_hr_permanent=[rep10], 461 available HR points, 24 orbits
- ALL 24 orbit representatives INFEASIBLE as singletons
- 461/461 HR points eliminated → 0 surviving HR points
- k=17 is closed at the SINGLETON level (no pair test needed!)
- Each singleton query took <1s (vs ~5-15s for rep2/rep16)
- Full k-descent k=16..2 is running

## Cross-k Monotonicity Validation
- If pair (h1,h2) is INFEASIBLE at k=k0, then INFEASIBLE at all k≥k0
- Proof: a valid (k+1)-point support minus one rank-1 gives a valid k-point support
- Contrapositive: infeasible at k ⟹ infeasible at k+1,...,18
- This means: k=16 pair exclusions for rep16 transfer to k=17 automatically
- But NOT the reverse: k=17 infeasibility does NOT imply k=16 infeasibility

## Mathematical Interpretation
The Wang occupation constraints are EXTREMELY tight at high rank-1 count:
- At k=17 (3 HR points), even individual HR singletons can't survive for rep10
- For rep2/rep16, singletons survive but ALL pairs are forbidden
- This means: the cumulative capacity cost of having many rank-1 factors
  (each occupying specific 1-dim subspaces) plus even 1-2 HR factors
  exceeds the Wang capacity bounds

The scientific question is: how far down in k can this continue?
At low k (many HR factors), the occupation pattern changes fundamentally.
The current k-descent experiments will reveal the critical transition.

## Running Background Tasks
1. Rep2/k=17 exhaustive pairs (~1000 classes): ALL tested so far INFEASIBLE
2. Rep10 full k-descent k=16..2: running
3. Rep16 full k-descent k=15..2: running

## Next Steps
1. Complete all background computations
2. If any branch closes fully (k=2..17), this gives R_{F_2} ≥ 21 (CP-SAT level)
3. Design proof-producing pipeline for closed levels:
   a. Combined k-level CNF with surviving variables only
   b. Individual singleton/pair DRAT proofs
   c. PB/VeriPB alternative
