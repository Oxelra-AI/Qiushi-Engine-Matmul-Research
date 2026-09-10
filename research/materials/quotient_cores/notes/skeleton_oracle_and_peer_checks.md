# fixed-k skeleton oracle repair, genuine joint-orbit pilot, and related analysis source checks

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Why this ARTIFACT was needed

analysis produced a faster vectorized skeleton prototype, but it had two distinct problems:

1. The original vectorized membership used the wrong pivot convention. This had already been patched to highest-set-bit pivots, but needed validation against the trusted exact-enumeration skeleton solver from analysis.
2. More importantly, the proposed 680 triple scan was not a valid symmetry reduction. Single-point orbits do not classify 3-subsets of higher-rank points; one common stabilizer element must move all points simultaneously. The set `{25,194,217}` that was already known from analysis has all three points in the single-point orbit represented by 25, so it is omitted by a scan over three distinct single-orbit representatives.

This ARTIFACT therefore preserved the useful part of the oracle while replacing the invalid orbit-label enumeration with fixed-rank1-count actual-set computations.

## New scripts and data

- [skeleton_oracle_joint_pilot.py](../code/skeleton_oracle_joint_pilot.py)
  - Builds the complete-LUT rank-1 completion oracle with fixed branch, fixed rank-1 count `k`, and fixed higher-rank subset `H`.
  - Uses corrected highest-set-bit vectorized membership.
  - Tests actual unordered subsets under the common stabilizer, not combinations of single-point orbit labels.
  - Extracts subset exclusions only at the same fixed `k`: if `H0` is infeasible for exact rank-1 count `k`, then any same-branch, same-`k` high set containing `H0` is also infeasible, because added higher-rank points only reduce residual capacities.

- [validate_vectorized_membership.py](../code/validate_vectorized_membership.py)
  - Compares vectorized membership with exact `subspace_points_from_basis` enumeration on a stratified/random sample.
  - Result: [vectorized_membership_random_validation.json](../results/skeleton_joint_pilot/vectorized_membership_random_validation.json).

- [high_subset_orbit_burnside.py](../code/high_subset_orbit_burnside.py)
  - Counts actual unordered higher-rank subset orbits by Burnside under the common branch stabilizer.
  - Result: [high_subset_orbit_burnside.json](../results/skeleton_joint_pilot/high_subset_orbit_burnside.json).

- [extract_forbidden_high_constraints.py](../code/extract_forbidden_high_constraints.py)
  - Converts INFEASIBLE fixed-`k` high-subset results into branch-stabilizer orbit-image master constraints.
  - Result: [forbidden_high_constraints.json](../results/skeleton_joint_pilot/forbidden_high_constraints.json).

The analysis prototype [precompute_skeleton_system.py](../code/precompute_skeleton_system.py) was edited only in its docstring to mark the single-point-orbit triple scan as superseded; the highest-set-bit membership routine remains available for import.

## Oracle validation

Main run:

```bash
PYTHONDONTWRITEBYTECODE=1 python -B scripts/skeleton_oracle_joint_pilot.py \
  --reps 2,16 --time-limit 15 --workers 8 \
  --out data/skeleton_joint_pilot/summary.json
```

Important output:

- The corrected vectorized membership agreed with exact enumeration in the built-in validation:
  - rep 2: 0 mismatches / 290 comparisons.
  - rep 16: 0 mismatches / 240 comparisons.
- A stronger random/stratified validation also found 0 mismatches over 67,392 comparisons, 468 sampled Wang rows, and 144 points:
  - [vectorized_membership_random_validation.json](../results/skeleton_joint_pilot/vectorized_membership_random_validation.json).

The fixed-k oracle reproduced the analysis known high-prefix eliminations in a stronger form: the full prefixes are infeasible, and in fact several 2-point high subsets already cause infeasibility at the same fixed `k`.

## Branch rep 2 results

Branch data:

- fixed rank-1 points: `[1,2]`.
- free rank-1 points: 47.
- available higher-rank points: 462.
- `|Stab(E11,2)| = 96`.
- single-point higher-rank orbits are still as in analysis: reps `[10,12,17,20,25,28,33,34,35,80,84,96,98,160,161,224,225]` with sizes 6--48. These are structural labels only, not a classification of tuples.

For the old k=17 high set `{25,194,217}`:

- all three points lie in the single-point orbit labelled 25;
- the actual set has canonical image `[25,193,218]` and orbit-image count 4;
- every pair inside this triple is already INFEASIBLE for exact rank-1 count k=17:
  - canonical `[25,193]`, orbit-image count 12.

Thus the high-pair constraint `sum_{h in g{25,193}} y_h <= 1` for all 12 branch-stabilizer images is a real family-level exclusion for the rep2/k=17 branch, subject to later proof-object conversion.

For the old k=16 high set `{34,52,278,304}`:

- labels are `[34,34,160,160]` and actual-set orbit-image count is 96;
- every pair among the four high points was INFEASIBLE for exact k=16, producing these canonical pair exclusions:
  - `[34,52]` (12 images),
  - `[34,274]` (96 images),
  - `[34,272]` (96 images),
  - `[34,400]` (96 images),
  - `[34,402]` (96 images),
  - `[160,274]` (96 images).

A genuine actual joint-orbit pilot for triples inside the single-point orbit 25 found exactly 3 joint orbits among the 20 raw triples. All 3 were INFEASIBLE for k=17:

- `[25,26,193]`, orbit-image count 12;
- `[25,193,217]`, orbit-image count 4;
- `[25,193,218]`, orbit-image count 4.

This pilot directly addresses the stratum omitted by the invalid 680 single-orbit-label scan; it should not be extrapolated to all triples.

## Branch rep 16 results

Branch data:

- fixed rank-1 points: `[1,16]`.
- parent branch excludes 30 earlier-orbit points, including 12 rank-1 points.
- free rank-1 points: 35.
- available higher-rank points: 444.
- `|Stab(E11,16)| = 32`.

For the old k=14 high set `{19,21,23,25,33,41}`:

- labels are `[19,20,20,19,33,33]`;
- actual-set canonical image `[19,20,22,25,33,41]`, orbit-image count 8;
- 10 of its 15 pairs were INFEASIBLE for exact k=14. Canonical exclusions:
  - `[19,20]` (8 images),
  - `[19,33]` (8 images),
  - `[20,22]` (4 images),
  - `[19,80]` (8 images),
  - `[20,41]` (8 images),
  - `[20,33]` (8 images),
  - `[20,49]` (8 images).
- The pairs `[19,25]`, `[23,33]`, `[25,33]`, `[25,41]`, `[33,41]` remained feasible as pair-level relaxations in this oracle run. They are not complete support candidates.

## Corrected orbit counts

Burnside counts in `high_subset_orbit_burnside.json` confirm the combinatorial scale under genuine joint orbits.

For rep2 (`462` higher-rank points, stabilizer order 96):

- 2-subsets: 1,376 joint orbits.
- 3-subsets: 174,453 joint orbits.
- 4-subsets: 19,580,358 joint orbits.
- 5-subsets: 1,788,605,676 joint orbits.
- 6-subsets: 136,181,792,356 joint orbits.

For rep16 (`444` higher-rank points, stabilizer order 32):

- 2-subsets: 3,520 joint orbits.
- 3-subsets: 460,637 joint orbits.
- 4-subsets: 50,039,855 joint orbits.
- 5-subsets: 4,394,617,098 joint orbits.
- 6-subsets: 321,444,862,332 joint orbits.

These counts show why full k=17/k=16/k=14 enumeration is not the right near-term research object. The useful object is a collection of small forbidden high patterns plus their actual stabilizer images, then a master search over higher-rank variables using those learned restrictions and the original Wang rows retained for eventual certification.

## Attempted proof-object conversion

I attempted to turn the rep2/k=17 canonical pair `[25,193]` into a CNF/DRAT proof with:

```bash
PYTHONDONTWRITEBYTECODE=1 python -B scripts/rank1_fixed_high_cnf.py \
  --fixed-rank1 1,2 --fixed-high 25,193 --exact-rank1-count 17 \
  --cnf data/pair_cnf/rep2_k17_pair_25_193/rep2_k17_pair_25_193.cnf \
  --meta data/pair_cnf/rep2_k17_pair_25_193/rep2_k17_pair_25_193.meta.json \
  --direct-comb-limit 2000 --solve --solver-time 600
```

The wrapper timed out after 1500 s only because it continued into `drat-trim`, but CaDiCaL itself had already solved the formula UNSAT in 57.5 s. Files:

- CNF: `workspace/data/pair_cnf/rep2_k17_pair_25_193/rep2_k17_pair_25_193.cnf`, 478,879 variables, 13,512,101 clauses, ~499 MB.
- DRAT: `workspace/data/pair_cnf/rep2_k17_pair_25_193/rep2_k17_pair_25_193.drat`, ~675 MB.
- Meta: [rep2_k17_pair_25_193.meta.json](../results/pair_cnf/rep2_k17_pair_25_193/rep2_k17_pair_25_193.meta.json).
- CaDiCaL log: `workspace/data/pair_cnf/rep2_k17_pair_25_193/rep2_k17_pair_25_193.cadical.log` contains `s UNSATISFIABLE` and exit 20.
- `drat-trim` was tried for 1800 s afterward and did not finish; its log is empty. Therefore this pair is not yet independently proof-checked, but the CaDiCaL run gives a concrete proof-object target.

Important caveat: `rank1_fixed_high_cnf.py` does not encode the rep2 parent branch directly, but for rep2 no parent points are excluded, so it matches this branch. It does include fixed rank-1 units `[1,2]` and exact total rank-1 count 17.

## Source checks from related analysis record

related analysis reported that Conner-Harper-Landsberg prove `underline R(M_<233>) = 14` and that this supplies a needed `R(M_<3,3,2>) >= 14` via border rank. I independently checked the local Knowledge object:

- `Knowledge/objects/papers/New-lower-bounds-for-matrix-multiplication-and--64a800eb2fe7--148396182a4c/object.md`, DOI `10.1017/fmp.2023.14`, lines 108--114 state:
  - `underline R(M_<223>) = 10`;
  - `underline R(M_<233>) = 14`.
- Since exact rank is at least border rank and matrix multiplication is cyclically equivalent under slot relabeling, this supports the chain
  `R(M_<3,3,2>) >= underline R(M_<3,3,2>) = underline R(M_<2,3,3>) = 14`
  over characteristic zero/complex settings where the CHL theorem is stated.

I also checked the border-rank-20 claim:

- `Knowledge/objects/papers/On-the-geometry-of-border-rank-algorithms-for-matrix-multiplication-and--7b14506d5a22--2db6af0f5886/object.md`, lines 57--60, especially Remark 2.1 line 58, records `19 <= R(M_<3>) <= 23` and `16 <= underline R(M_<3>) <= 20`, with the upper bound cited to [29] (Smirnov).
- CHL improves the lower side to 17 (line 97 of the CHL object), so current complex border-rank bounds are `17 <= underline R(M_<3>) <= 20`. The upper bound 20 does not by itself exclude exact rank 22; it only explains why degeneration/noncompact behavior is natural if exact rank is above 22.

## Scientific state after this ARTIFACT

No rank-22 exact algorithm and no rank-23 optimality proof has been obtained. The finite-field Wang route remains a necessary-support search, not a tensor-rank theorem beyond Wang's verified `R_F2 >= 20`. The ARTIFACT did make three concrete advances:

1. The vectorized skeleton oracle is now validated against exact membership samples and known analysis eliminations.
2. The invalid single-point-orbit triple reduction has been replaced with actual-set symmetry, with Burnside counts quantifying the true search scale.
3. Several small, reusable high-pair exclusions were found for rep2/k=17, rep2/k=16, and rep16/k=14, with branch-stabilizer images saved in `forbidden_high_constraints.json` and underlying witness Wang rows in the summary.

The next productive work is to build a master high-subset search that uses these small forbidden patterns and selected original Wang rows, rather than enumerating all high-subset joint orbits. In parallel, the rep2/k=17 pair `[25,193]` CNF target should be made smaller or independently checked, since it is a concrete proof-producing route for one family-level exclusion.
