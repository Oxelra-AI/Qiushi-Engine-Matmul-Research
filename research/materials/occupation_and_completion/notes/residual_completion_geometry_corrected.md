# corrected residual completion geometry

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Why this note replaces the earlier analysis interpretation

The residual-space idea is valuable, but the first analysis note overstated the
free-A/B local exclusions.  review found two substantive issues, both now adopted
as corrections:

1. When `d = dim(E) < k`, successful repair vectors need not individually lie
   in `E`; their components in the quotient by `E` can cancel.  Therefore
   tag-span inside `E` is a complete condition only in the exact case `d=k`.
2. The first free-A/B script used a quotient remainder routine that stopped at
   the first non-pivot bit.  That remainder was not linear, so kernel/tag-rank
   numbers from `free_ab_k_scan.py` and the old `k=5` cn122 output are
   not reliable as exclusion evidence.

The corrected implementation is
[free_ab_k_scan_corrected.py](../../quotient_cores/code/free_ab_k_scan_corrected.py).  It uses a canonical
linear reduction that eliminates every pivot bit and records `d<k` blocks as
unresolved by this method.

## Mathematical reduction retained

For fixed retained columns
\[
L=\operatorname{span}\{a_i\otimes b_i: i\text{ retained}\}\subset
\mathbb F_2^{81},
\]
let
\[
E=\pi(\operatorname{col}(D))\subset \mathbb F_2^{81}/L,
\]
where `D` is the `(A,B)|C` flattening of `T_<3,3,3>`.  A repair block of `k`
new columns can complete the tensor only if `E` lies in the span of their images.

Safe conclusions:

* `d>k` is an exact obstruction for that retained-column block.
* For fixed-A slots and `d=k`, define
  \[
  H_t=\pi(a_t\otimes \mathbb F_2^9)\cap E.
  \]
  A repair exists exactly when the vector-matroid Hall/Rado inequalities hold:
  for every slot subset `J`,
  \[
  \dim\sum_{t\in J}H_t\ge |J|.
  \]
* For free A/B slots and `d=k`, each slot can use any rank-one matrix
  `a\otimes b`; the local repair exists exactly when the tags in `E` of
  rank-one columns lying in `L+E` span `E`.  Any tag-span witness is lifted to
  `(A,B)`, then `C` is solved from `K C^T=D`, and the full Brent tensor identity
  is verified.
* `d<k` is not settled by the above tag-span-in-`E` test; handling it requires
  tracking the full quotient components and their cancellation, for example by
  a small exact search/SAT over the quotient of dimension `d + outside`.

## Controls

The one-column positive control remains valid:
[residual_positive_control.json](../../quotient_cores/results/residual_repair/residual_positive_control.json)
recovered all 23 deleted terms of `cn122` as rank-23 one-slot repairs with
`brent_diff=0`.

The corrected free-A/B script adds multi-column controls restricted to `d=k`,
where the E-intersection path is the intended exact test.  For `cn122_qmm` it
reports `ok_d_eq_k=1970`, `total_d_eq_k=1970`, `all_d_eq_k_ok=true`, and
`skipped_d_lt_k=77` across the original rank-23 deletion controls of sizes
1, 2, and 3.  The skipped controls are exactly the cancellation-bearing `d<k`
cases and are not failures.

## Corrected local scan results so far

### Fixed-A/B-only scans

The earlier fixed-A residual script already marked `d<k` as `UNDERDETERMINED`.
The strict content from `workspace/data/residual_repair_k3/` is:

* `d>k` blocks are impossible.
* `d=k` Hall-fail blocks are impossible.
* `d<k` blocks remain open for this residual method.

No rank-22 witness was found in these B-only neighborhoods.

### Peer deletion-seeded A-swap candidates

For six peer candidates in `data/pipeline_results`,
changing B only in the A-swapped slots gives `d=k+1`; these narrow repairs are
impossible.  Adding one or two extra B-changing slots produced 186 exact `d=k`
Hall failures and 996 `d>k` impossibilities, but four `d<k` cases remain
unsettled.  No witness was found.

### Corrected free-A/B scans near cn122

The old free-A/B `k=5` artifact is superseded; the corrected `k=5` run is
currently managed as task `s29_t57_tool1`.

Corrected cn122 `k=3` free-A/B scan:

```
d4_gt_k              31956
exact d3 blocks:      tagrank2 2488, tagrank1 876, tagrank0 80
d2_lt_k_tagrank0        20   (unsettled by this method)
rank22 witnesses          0
```

Path: [free_ab_k3_scan_corrected.json](../../quotient_cores/results/free_ab_corrected_k3/free_ab_k3_scan_corrected.json).

Corrected cn122 `k=4` free-A/B scan:

```
d5_gt_k             136405
exact d4 blocks:     tagrank3 19020, tagrank2 10035,
                     tagrank1 1835, tagrank0 230
d3_lt_k blocks:      tagrank0 240, tagrank1 480   (unsettled)
rank22 witnesses         0
```

Path: [free_ab_k4_scan_corrected.json](../../quotient_cores/results/free_ab_corrected_k4/free_ab_k4_scan_corrected.json).

For the exact `d=k` blocks, these are local exclusions of free A/B repairs that
retain the complementary old columns from `cn122`.  They do not exclude the
`d<k` blocks and do not speak to rank-22 schemes far from the retained-column
neighborhood.

## Scientific meaning

The residual representation is a useful way to keep constructive information
from a rank-23 decomposition while allowing controlled changes.  The corrected
results show that many very local repairs fail for structural reasons: the
rank-one column images do not span the residual target in the exact-dimensional
case.  This is a precise local phenomenon, not evidence that rank 23 is globally
optimal.

The next constructive work should either solve the `d<k` cancellation cases by
tracking full quotient coordinates, or develop a global search that directly
maximizes residual coverage while changing many columns.  The peer's fixed-A
filters and Wang hill-climber should be compared with this residual geometry:
Wang-admissible A-lists are not enough, and local repairs that preserve too many
old columns appear too rigid, but neither observation closes the rank-22
possibility.

The lower-bound route remains separate and unfinished.  Its substantive open
burden is pivot/rank-two branches 0 and 2, pivot/rank-three branch 0, plus
independent certification of the rank-two branch 1 infeasibility report.
