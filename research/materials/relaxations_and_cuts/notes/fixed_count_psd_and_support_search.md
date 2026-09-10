# fixed-count second-moment repair and point-level support search

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Scientific target

The unresolved finite-field branch is still the distinct 19-direction projected-A support in the E11 quotient core.  Excluding all such supports would establish the next finite-field lower-bound ARTIFACT through the existing full-to-core bridge; finding a valid support would trigger fixed-A/B/C completion and might lead to a rank-19 E11 core, hence a full rank <=22 algorithm after adding the deleted E11 slice terms.

analysis made an important computational advance by block-decomposing the 256 x 256 labelled moment matrix into 93 small PSD blocks.  However, its handoff overstated the model tested.  Fixing `x_a = n_a/|O_a|` fixes only integer *mean* orbit counts.  Averaging a single actual support over the stabilizer preserves each orbit count in every sample, so it also imposes deterministic block-pair totals and forced kernels

\[
  \sum_{P_j\subset O_a\times O_b} |P_j| y_j = n_a n_b \quad (a<b),
\]
\[
  \sum_{P_j\subset {O_a\choose 2}} |P_j| y_j = \binom{n_a}{2},
\]

equivalently
\[
  M(-n_a,1_{O_a})^T=0.
\]

The 23 scalar PSD blocks are pair-moment constraints, not point-only cuts in the 255 support variables.

## Fixed-count + block-total + PSD test

New script:

- [fixed_count_block_psd.py](../code/fixed_count_block_psd.py)

Output:

- [fixed_count_block_psd_results.json](../results/fixed_count_block_psd/fixed_count_block_psd_results.json)
- saved continuous witnesses for three count vectors:
  - [n_0_0_3_5_4_7_z.npy](../arrays/fixed_count_block_psd/n_0_0_3_5_4_7_z.npy)
  - [n_1_0_3_6_2_7_z.npy](../arrays/fixed_count_block_psd/n_1_0_3_6_2_7_z.npy)
  - [n_1_0_4_5_2_7_z.npy](../arrays/fixed_count_block_psd/n_1_0_4_5_2_7_z.npy)

The script reused the analysis block decomposition and imposed, for each fixed count vector:

1. analysis Wang RLT rows: 183,302 upper-bound inequalities;
2. analysis triangle/Fortet rows: 5,913 inequalities;
3. deterministic block-pair total equalities: 21 rows;
4. block-decomposed labelled moment PSD: 23 scalar blocks + 70 matrix blocks, largest block 7.

It tested 33 count vectors: the 30 analysis nearby count vectors plus three analysis integer block-count witnesses.  Results:

- 6 count vectors had numerical continuous fixed-count/block-total/PSD witnesses (`optimal_inaccurate` but residuals small):
  - `[0,0,3,5,4,7]`
  - `[1,0,3,6,2,7]`
  - `[1,0,4,5,2,7]`
  - `[1,0,3,6,3,6]`
  - `[2,0,3,5,3,6]`
  - `[1,0,4,5,3,6]`
- 14 were reported `infeasible` by CLARABEL.
- 13 produced a CLARABEL solver error and must remain unresolved unless retested.

For the first three saved witnesses, full labelled-matrix checks gave:

- linear equality residuals around `6.5e-13` to `3.8e-11`;
- maximum linear upper-bound excess around `6.8e-11` to `1.0e-10`;
- block-total residuals around `4.0e-11` to `8.6e-10`;
- forced-kernel residuals around `1.0e-11` to `3.3e-11`;
- no eigenvalue below `-1e-8` in the full 256 x 256 matrix.

A separate check of the saved matrices confirmed that the only negative eigenvalues are numerical-scale (roughly `-5e-11` to `-4e-12` for the first three).  The forced kernels `(-n_a,1_{O_a})` are present to numerical precision.  These are not exact rational feasibility certificates, but they are strong numerical witnesses that deterministic orbit-count kernels do not by themselves close the second-moment relaxation.

The saved witnesses have highly nonintegral pair counts `m_j=|P_j|y_j`: maximum distance to an integer about `0.49--0.50`, total distance about `17--22`.  Thus integer pair-count realizability remains a real missing layer.

## Integer pair-count PSD pilot

New script:

- [fixed_n_integer_pair_psd_loop.py](../code/fixed_n_integer_pair_psd_loop.py)

Output:

- [integer_pair_psd_loop.json](../results/integer_pair_psd_loop/integer_pair_psd_loop.json)

For two promising continuous-survivor count vectors `[0,0,3,5,4,7]` and `[1,0,3,6,2,7]`, I asked CP-SAT for exact integer pair-orbit counts satisfying:

- fixed `n`;
- integer `m_j`;
- block pair totals;
- all Wang RLT rows and triangle rows exactly after scaling by 1152.

Each returned integer pair-count assignments satisfying the linear conditions exactly, but their labelled moment matrices were strongly non-PSD.  Four rounds with numerical square cuts for each count did not find a PSD integer pair-count witness:

- `[0,0,3,5,4,7]`: min eigenvalues `-0.3646`, `-0.1371`, `-0.1564`, `-0.07036`;
- `[1,0,3,6,2,7]`: min eigenvalues `-0.3646`, `-0.09610`, `-0.1264`, `-0.1257`.

The square cuts in this pilot are floating rounded search cuts only, not certified inequalities.  Failure to find an integer PSD pair witness in this small loop is not an exclusion.  It does show that pair integrality plus PSD is a much sharper layer than the continuous block-total SDP.

## Point-level actual support search

New script:

- [count_target_support_search.py](../../occupation_and_completion/code/count_target_support_search.py)

Output:

- [targeted_count_support_search.json](../../occupation_and_completion/results/count_target_support_search/targeted_count_support_search.json)

I ran the original 255 Boolean support problem under four targeted count branches:

- three continuous fixed-count/block-total/PSD survivors:
  - `[0,0,3,5,4,7]`
  - `[1,0,3,6,2,7]`
  - `[1,0,4,5,2,7]`
- the analysis closest near-support count:
  - `[3,0,15,1,0,0]`

The model included:

- all 416,416 nontrivial complete E11 Wang rows from the 417,199-row table;
- fixed point-orbit counts;
- 3,456 transported verified face cuts;
- 1,152 transported overlap cuts;
- 255 contraction lower bounds.

Each branch was run for about 240 seconds with 8 workers.  All four returned `UNKNOWN`; no actual support and no proof was produced.  The `UNKNOWN` statuses are search evidence only.  No fixed-A/B/C completion was reached because no complete-Wang support was found.

## Consequences for the research state

1. The analysis broad conclusion that the whole second-moment route is closed was too strong and has been corrected.
2. The fixed-count deterministic block-total / forced-kernel gap has now been tested on a bounded set, and the continuous version survives in several branches.  This supports moving beyond that precise continuous relaxation for those counts, while keeping exact feasibility unclaimed.
3. Integer pair-count + PSD remains unresolved.  The small pilot found only non-PSD integer pair assignments, despite exact satisfaction of Wang RLT and block totals.  This suggests a concrete next layer: develop a better mixed-integer PSD separation/search for `m_j`, ideally with rationalized square cuts or a proof-producing PB/SAT encoding of chosen PSD cuts.
4. The actual point-level distinct support problem remains open.  Targeted complete-Wang searches under four count branches returned `UNKNOWN`, not a lower bound and not a support.
5. The finite-field frontier is unchanged:
   \[
   20 \le R_{\mathbb F_2}(T_{\langle3,3,3\rangle}) \le 23.
   \]
   No rank-19 E11 core identity, no rank <=22 full algorithm, and no complete exclusion of distinct E11 projected-A supports has been obtained.

## Useful next work

The most valuable continuation is not blind square-cut accumulation, but a coordinated attack on the now sharpened gap between continuous second moments, integer pair counts, and actual point supports:

- strengthen the integer-pair PSD loop with exact rational square cuts from negative eigenvectors and use it to test all six continuous fixed-count survivors;
- for any fixed count with a PSD integer-pair witness, attempt point-level graph/color realization before B/C completion;
- for any fixed count where integer-pair PSD appears impossible, try to obtain a small rational square-cut certificate rather than relying on CLARABEL or rounded CP-SAT statuses;
- keep the 255-variable support search active, especially under count vectors surviving the continuous model, but treat timeouts as unresolved and found supports as A-support candidates requiring full Wang rescan and fixed-A/B/C rank-one completion.
