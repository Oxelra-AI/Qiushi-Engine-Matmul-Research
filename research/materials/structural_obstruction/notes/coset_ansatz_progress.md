# coset-ansatz execution notes

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Purpose

The analysis coset theorem reduced a hypothetical rank-20 full decomposition to a highly structured high-rank A-factor configuration. This ARTIFACT tested the refinement: the dim-4 quotient route cannot prove a stronger bound because the quotient by the row-1 subspace is `T_{<2,3,3>}` and Wang's dim-4 value 14 is exact after quotienting by a rank-2 image. The useful remaining question is whether the surviving zero-excess coset configuration is compatible with the full A-side Wang rows.

## Exact table checks

Existing [coset_closure_v2.json](../results/coset_analysis/coset_closure_v2.json) already contains the exact table requested by the review:

- all 651 coset-derived dim-3 spans have exact Wang lower bound 17, not 18: `dim3_span_lb_dist = {"17": 651}`;
- all 63 dim-4 coset spans have Wang LB 14.

Therefore the possible shortcut via four planes with LB 18 does not occur.

## Normalized surviving configuration

I wrote [surviving_coset_ansatz.py](../code/surviving_coset_ansatz.py). It fixes the column-type coset with

- `p = 272` (lower block rank 2, first row zero),
- `S = <272,1,2,4>` with Wang LB 14,
- rank-2 coset elements `{272,274,276,278}` and rank-3 elements `{273,275,277,279}`.

The script enumerates the only surviving high-rank sets `H`: one rank-2 element and three rank-3 elements, with no affine plane among their first-row labels. There are 16 such configurations. For all 16:

- every one of the six pair spans has Wang LB 18;
- every one of the four triple spans has Wang LB 17;
- the six first-row rank-one directions appearing as pair differences are forbidden for additional rank-one factors; exactly one first-row rank-one direction remains allowed;
- the initial local LUT filters leave 43 allowed rank-one directions total (the one remaining first-row point plus all 42 rank-one points outside the first-row family).

The analysis output is [surviving_coset_ansatz.json](../results/coset_ansatz/surviving_coset_ansatz.json).

The affine-plane count in AG(3,2) was also recomputed: a 5-subset contains 1 plane, a 6-subset contains 3 planes, a 7-subset contains 7 planes, and the whole 8-set contains 14; a 4-subset contains either 0 or 1 plane. This supports the reduction to the 16 four-point non-plane configurations.

## Full A-side Wang closure for the surviving rank-one part

For each of the 16 normalized `H` cases, the same script ran a CEGAR loop over the complete length-20 full Wang binary `workspace/data/wang_native/full_tensor/full_wang512_cap19_len20_all_dim9_allbinding.bin`:

- choose exactly 16 distinct rank-one directions from the 43 allowed points;
- impose per-left and per-right rank-one line caps of 5;
- scan all 8,283,456 full Wang rows and add violated rows.

All 16 cases became CP-SAT infeasible after 3 or 4 candidate supports (4 for H00, 3 for the other 15). The summary is [cegar_16_summary.json](../results/coset_ansatz/cegar_16_summary.json). Candidate supports before closure had hundreds to about 1,700 violations, mostly in dimensions 4--7.

I then performed an independent SciPy LP/MILP audit of the active CEGAR closures using [coset_active_constraint_audit.py](../code/coset_active_constraint_audit.py) and [coset_ansatz_batch_audit.py](../code/coset_ansatz_batch_audit.py). For all 16 normalized cases, the active-row LP relaxation remains feasible, but the integer MILP is infeasible; the batch result is [cegar_16_batch_audit.json](../results/coset_ansatz/cegar_16_batch_audit.json). For H00 specifically, the closure used 3,542 active Wang rows and HiGHS MILP proved infeasibility in 1.54 s after reconstructing the active rows; all 16 independent MILPs returned infeasible.

I also ran a transpose/row-type batch [surviving_coset_transpose_batch.py](../../symmetry_and_residuals/code/surviving_coset_transpose_batch.py). It transposes the same 16 high-rank sets and repeats the full A-side CEGAR. All 16 row-type cases likewise close as CP-SAT infeasible, saved under [transpose_batch_summary.json](../../symmetry_and_residuals/results/coset_ansatz/transpose_batch/transpose_batch_summary.json); a single transposed H00 independent MILP audit is [audit_transpose_H00.json](../../symmetry_and_residuals/results/coset_ansatz/audit_transpose_H00.json).

## Dim-2 raises under original LUT

The dim-2 raises are premises of the lower-bound chain. I reran [node_local_occupation_closure.py](../../quotient_cores/code/node_local_occupation_closure.py) with the original Wang LUT and a longer 900 s per-node time limit:

[dim2_raise_original_900s.json](../../finite_certification/results/wang_analysis/node_local/dim2_raise_original_900s.json)

Results:

- 478 infeasible at old LB 17 (not central for the refined chain);
- 479 and 484--491 infeasible at length 18 under the original LUT, so these raise to 19 by occupation rows alone;
- 480, 481, 482, 483 are feasible at length 18; 482 and 483 were previously UNKNOWN at 20 s and are now confirmed feasible, so no accidental closure is hidden there.

An independent SciPy audit at 120 s left 479 unresolved by HiGHS MILP, while confirming the other easy infeasibilities; the CP-SAT rerun is currently the stronger evidence for 479.

## Important status

The current results are mathematically very promising but still need proof-quality packaging and independent replay:

- The 16+16 surviving coset closures are complete A-side Wang occupation exclusions for the normalized column/row cases, but the CEGAR active-row systems are not yet proof certificates. They need a compact reproducible certificate format and independent peer replay, or a derivation that converts the active rows into a directly checkable combinatorial contradiction.
- The dim-2 raises 479 and 484--491 need the same certification and peer replay. A simple Boolean slot CNF encoding for node-local raises was attempted in `node_local_to_cnf.py`, but the naive encoding is huge (~1.47 GB for node 485) and CaDiCaL did not solve it in 60 s. A more compact PB/CP certificate or custom DFS proof logging is needed.
- No final lower-bound theorem is yet established until the coset reduction, row/column transposition coverage, active-row closures, and dim-2 raises are independently verified as exact mathematical statements.
