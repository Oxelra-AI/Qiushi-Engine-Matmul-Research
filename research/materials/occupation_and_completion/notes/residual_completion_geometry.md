# residual completion geometry for rank-22 search

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Purpose

The previous linear completion work introduced the matrix
\[
K=[a_1\otimes b_1|\cdots|a_r\otimes b_r]\in \mathbb F_2^{81\times r},
\]
with target flattening `D` of `T_<3,3,3>`.  For fixed `A,B`, completion in the
`C` slot is exactly the linear system `K C^T = D`.  This note records the
analysis correction: random-B maximum defect and small failed neighborhoods do
not imply likely optimality of rank 23.  What is useful is an exact residual
quotient test for local repairs.

## Exact residual-space reduction

Fix a set of retained old columns `L = col(K_retained)`.  Let
\[
E=\pi(\operatorname{col}(D)) \subset \mathbb F_2^{81}/L.
\]
For a repair slot with fixed A-factor `a_t`, define
\[
U_t=\pi(a_t\otimes \mathbb F_2^9).
\]
If a smaller valid B-domain is available, replace `F_2^9` by that linear domain.
Completion by a k-slot block requires choosing `v_t in U_t` such that `E` is
contained in the span of the chosen vectors.

Consequences:

* If `dim(E)>k`, the block is impossible immediately.
* If `dim(E)=k`, every successful vector must lie in `E` and the selected
  vectors must be a basis of `E`.  For fixed-A slots this is the subspace
  independent-transversal condition: for every subset `J`,
  `dim(sum_{t in J} (U_t cap E)) >= |J|`.
* For free A/B slots, every repair slot has the same attainable set: images in
  `E` of rank-one `9x9` matrices `a\otimes b`.  If that attainable set spans
  `E`, one can choose representatives, solve for `C`, and verify all Brent
  equations.  If it does not span `E`, that retained-neighborhood is exactly
  impossible.  This is complete whenever the block size is at least `dim(E)`;
  if `dim(E)>k` the dimension obstruction applies.

A positive control was run: retain 22 columns of the verified `cn122` rank-23
scheme, add the original deleted term as a one-slot repair.  All 23 deletions
were recovered and verified (`ok_count=23/23`).  File:
[residual_positive_control.json](../../quotient_cores/results/residual_repair/residual_positive_control.json),
SHA256 `281939f640ed88b8b95925e72178dccd04be4f217a3098210fc0e0709bf493ae`.

## Fixed-A residual tests around peer A-swap candidates

Script: [residual_repair_geometry.py](../../quotient_cores/code/residual_repair_geometry.py)
(SHA256 `31f2d3cd84c784fa21901b41014fecdfc6869d9e2ab3e22f55f6cb6d0181efa1`).

For six deletion-seeded peer candidates in
`data/pipeline_results/pipeline_summary.json`, the
first test allowed B changes only in the slots where the peer Wang hill-climber
changed A relative to the rank-23 deletion seed.  Every candidate had
`dim(E)=k+1`, so that narrow repair is impossible:

* 2 changed slots -> `d=3`.
* 3 changed slots -> `d=4`.

Adding one or two extra unchanged B-changing slots gave:

```
status_hist: IMPOSSIBLE_D_GT_K 996, NO_REPAIR_HALL_FAIL 186,
             UNDERDETERMINED_D_LT_K 4
exact_hist:  d_eq_k 186, hall_fail 186, d_gt_k 996, d_lt_k 4
```

No rank-22 witness was produced.  The four `d<k` cases are not exclusions;
they had zero attainable residual tag rank in the simple sufficient test.
File: [pipeline_extra_repair_scan.json](../../quotient_cores/results/residual_repair/pipeline_extra_repair_scan.json).

## B-only retained-neighborhood scans

For three verified rank-23 sources (`cn122_qmm`, `flip_rank23_text`, and the
pivot17 transform), all one-, two-, and three-slot B-only retained-column
repairs were checked exactly by the residual quotient test.

For `k<=3`:

* `cn122_qmm`: `k1` had 500 `d>k` and 6 Hall failures; `k2` had 5091 `d>k` and
  222 Hall failures; `k3` had 31956 `d>k`, 3444 Hall failures, and 20 `d<k`.
* `flip_rank23_text` and `pivot17_transformed_rank23`: `k1` all 506 `d>k`;
  `k2` had 5277 `d>k` and 36 Hall failures; `k3` had 34348 `d>k` and 1072 Hall
  failures.

No witness.  File:
[residual_repair_geometry.json](../../quotient_cores/results/residual_repair_k3/residual_repair_geometry.json).

## Free A/B retained-neighborhood scans

Scripts:

* [ab_residual_block_search.py](../../quotient_cores/code/ab_residual_block_search.py), SHA256
  `d8e1b13b1f1e51eccb1b30d713ad25bad0938820cf3bceb438e4a494c152cc0a`.
* [free_ab_k_scan.py](../../quotient_cores/code/free_ab_k_scan.py), SHA256
  `0a2dc2f1b6e160af386263be0e446936ce7160bdb77d7beeb17d96e55c01f144`.

These scans allow A and B to change freely in the repair block while all other
old K columns are retained.

### k=1,2 over three verified rank-23 sources

No witness.

* `cn122_qmm`: `k1`: 500 `d=2`, 6 no attainable tag; `k2`: 5091 `d=3`, 33 empty
  residual intersection, 189 no independent tags.
* `flip_rank23_text` and `pivot17_transformed_rank23`: `k1`: 506 `d=2`; `k2`:
  5277 `d=3`, 36 empty residual intersection.

File: [ab_residual_block_search.json](../../quotient_cores/results/ab_repair/ab_residual_block_search.json).

### k=3

No witness.

* `cn122_qmm`: 31956 blocks with `d>3`; exact `d<=3` blocks had tag-rank at
  most 2 (`d3_tagrank0=1112`, `d3_tagrank1=1768`, `d3_tagrank2=564`, plus
  `d2_tagrank0=20`).
* `flip_rank23_text`: 34348 blocks with `d>3`; exact blocks had tag-rank at most
  2 (`d3_tagrank0=696`, `d3_tagrank1=376`).
* `pivot17_transformed_rank23`: same `d>3` count, with `d3_tagrank0=612`,
  `d3_tagrank1=460`.

Files:
[free_ab_k3_scan.json](../../quotient_cores/results/free_ab_k3/free_ab_k3_scan.json) and
[free_ab_k3_scan.json](../../quotient_cores/results/free_ab_k3_other/free_ab_k3_scan.json).

### k=4

No witness.

* `cn122_qmm`: 136405 blocks with `d=5>k`; exact `d<=4` blocks had tag-rank at
  most 3 (`d4_tagrank3=1850` was the largest class, still below `d=4`).
* `flip_rank23_text`: 154005 blocks with `d=5>k`; exact blocks had tag-rank at
  most 2.

Files:
[free_ab_k4_scan.json](../../quotient_cores/results/free_ab_k4/free_ab_k4_scan.json) and
[free_ab_k4_scan.json](../../quotient_cores/results/free_ab_k4_flip/free_ab_k4_scan.json).

### k=5 cn122

No witness.  File:
[free_ab_k5_scan.json](../../exact_baselines/results/free_ab_k5_cn122/free_ab_k5_scan.json), SHA256
`795f27e186c1a34a2fe5f951eeb58cf145fde14c0dc613f95b58dce509e8dcfd`.

Aggregate:

```
d6_gt_k       409092
exact d5: tagrank0 15300, tagrank1 61944, tagrank2 73530,
          tagrank3 30642, tagrank4 3672
exact d4: tagrank0 5082, tagrank1 5370, tagrank2 1002
exact d3: tagrank0 48
```

Thus among all five-slot retained-column neighborhoods of `cn122`, the image of
all rank-one A/B replacements never spans the residual target `E`; it reaches
rank 4 in some five-dimensional residuals but never rank 5.

## Interpretation

These are meaningful construction-side exclusions, but they are local: they
exclude rank-22 schemes obtained by retaining at least 17 old K-columns from the
specific verified rank-23 seed(s) and freely changing the remaining terms.  They
do not prove rank 23 optimal and do not exclude rank-22 decompositions far from
these seeds, nor coordinated changes that keep fewer old columns.

The most useful scientific insight is that the residual obstruction is not just
that fixed old A values have poor B repair.  Even when A and B are both allowed
to vary freely in up to five changed slots near `cn122`, the rank-one image in
the quotient by retained columns does not span the missing D-space.  This gives
a precise geometry for why local deletion/repair of known rank-23 algorithms is
hard, and it suggests that any rank-22 construction may require a more global
reorganization of the K columns rather than a small repair of a known rank-23
scheme.

Future work should either (a) use this residual-space representation to guide a
global construction search that tries to maintain residual tag-span while
changing many columns, or (b) return to the lower-bound route with genuinely
lift-coupled proof objects rather than longer unchanged quotient DFS runs.  The
remaining lower-bound burden is rank-two branches 0 and 2, rank-three branch 0,
and independent certification for rank-two branch 1.
