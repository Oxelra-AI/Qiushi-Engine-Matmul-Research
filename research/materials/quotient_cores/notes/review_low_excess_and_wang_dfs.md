# review Review — generalized low-excess geometry and Wang-support DFS

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

research: research_record. Field: $\mathbb F_2$. Object: E11 quotient core of $T_{\langle3,3,3\rangle}$.

## 1. Generalized low-excess contraction geometry

I independently reviewed [general_low_excess_filter.py](../code/general_low_excess_filter.py) using a separate checker, [general_low_excess_review.py](../code/general_low_excess_review.py), and an independent review verifier reading the analysis/analysis artifacts.

The mathematical core is sound for a fixed labelled A-list with nonzero rank-one terms. For a quotient dual direction $\lambda$ represented by a $3\times3$ matrix $\Lambda$ with the missing E11 coordinate zero, the contracted B/C matrix is
\[
M_\lambda=\Lambda^T\otimes I_3,
\]
so over $\mathbb F_2$
\[
\operatorname{rank} M_\lambda=3\operatorname{rank}\Lambda.
\]
If $m$ terms are active under $\lambda$ and an exact core factorization exists, then with $r=\operatorname{rank}M_\lambda$ and prescribed spaces
$U_\lambda=\operatorname{col}(M_\lambda)$, $V_\lambda=\operatorname{row}(M_\lambda)$, Sylvester's inequality gives
\[
e_B(\lambda)+e_C(\lambda)\le m-r,
\]
where $e_B=\dim(\langle b_t:t\in I_\lambda\rangle/U_\lambda)$ and similarly for $C$.

When $m=r$, the active B-vectors and C-vectors are independent bases of $U_\lambda$ and $V_\lambda$. If such a tight source $\lambda$ shares $h$ labelled terms with another contraction $\mu$, then every exact completion must satisfy
\[
e_B(\mu)\ge \max(0,h-\dim(U_\lambda\cap U_\mu)),\qquad
e_C(\mu)\ge \max(0,h-\dim(V_\lambda\cap V_\mu)).
\]
The analysis use of maxima over tight sources is conservative and valid. It does not add unsupported sums of leakage dimensions from unrelated sources.

The purity-variable clauses are also sound as necessary conditions:

- $m=r$ forces both side-purities;
- $m=r+1$ forces at least one side-purity;
- positive leakage lower bound forbids the corresponding side-purity;
- saturation of one side's leakage budget forces the other side pure;
- if two contractions share a labelled nonzero term and their prescribed B-spaces (or C-spaces) intersect only at zero, they cannot both be pure on that side.

The analysis script treats repeated A-directions as labelled terms and therefore does not silently collapse sums of rank-one B/C matrices. This is important: repeated quotient directions can occur in local fixed-A examples even though the lower-bound route later separates the repeated projected-A branch using the replayed certificate.

## 2. Limits and corrections to the analysis results

[general_low_excess_filter_samew_full.json](../results/general_low_excess/general_low_excess_filter_samew_full.json) reports that 814 same-W two-deletion A-lists were scanned; 54 passed both shadow consistency and coordinate purity; all 54 were rejected by the generalized low-excess filter. This is useful fixed-A-list evidence, not a global statement about all rank-19 E11 supports. The same-W lists come from known rank-21 cores by deleting two equal-W terms and are not a cover of the target branch.

The new content inside those 54 rejections is mixed:

- 37 of the 54 have both ordinary scalar contraction deficits and leakage-budget contradictions;
- 17 of the 54 have no scalar contraction deficit and are rejected by leakage-budget contradictions alone.

Thus the 17 scalar-clean cases are the clearest evidence that generalized leakage adds information beyond the ordinary contraction rank counts and coordinate purity.

The analysis result field `2sat_sat=false` is ambiguous when the script has already hard-rejected a support by scalar or leakage contradiction, because in that case the implication graph is not actually solved. Future outputs should separate scalar deficit, leakage-budget contradiction, and purity-graph satisfiability with a three-state field for the latter.

Rank-3 tight contractions are valid as additional leakage sources: their prescribed spaces are the full 9-dimensional B/C spaces, so their purity variables are vacuous, but if exactly nine terms are active then those B/C factors form full bases and can constrain rank-one or rank-two target contractions by the same shared-term argument. analysis omitted these sources; this makes the filter weaker, not unsound. analysis pool tests found 509 of 519 rank-21 pool rows have rank-3 tight sources not used by analysis, and adding them did not create a false rejection on the verified pool. L15 and analysis have rank-3 tight sources but still no generalized leakage contradiction.

Core artifacts:

- [general_low_excess_review.py](../code/general_low_excess_review.py)
- [general_low_excess_review.json](../results/general_low_excess/general_low_excess_review.json)
- review integration: `independent-verification-record`

## 3. Peer coding-theory/Wang-support work

I reviewed research_record record and the files `e11_ghw_singleton_test.py`, `e11_wang_dfs_enumerator.py`, and `e11_cap3_stream_check.py`. I rebuilt the E11 quotient Wang table independently using the canonical `CoreQuotient.key9_from_key8` interface in `scripts/core_capacity_from_wang_lut.py`.

The generalized-Hamming-weight computation is correct and matches exactly. For a 19-term distinct quotient A-support, the columns span an 8-dimensional binary code because all columns lying in a hyperplane would violate the E11 Wang row with lower bound at least 3. For an $r$-dimensional dual subspace, the Wang occupation bound gives a lower bound $L_r$ on the $r$-th generalized Hamming weight. The canonical values are:

| $r$ | dim8 | $L_r$ | Singleton $11+r$ | gap |
|---:|---:|---:|---:|---:|
| 0 | 8 | 0 | 11 | 11 |
| 1 | 7 | 3 | 12 | 9 |
| 2 | 6 | 6 | 13 | 7 |
| 3 | 5 | 9 | 14 | 5 |
| 4 | 4 | 11 | 15 | 4 |
| 5 | 3 | 14 | 16 | 2 |
| 6 | 2 | 15 | 17 | 2 |
| 7 | 1 | 17 | 18 | 1 |
| 8 | 0 | 19 | 19 | 0 |

There is no Singleton contradiction. This reframing clarifies the pressure from Wang rows but does not decide support existence.

For $s=19$, the canonical E11 quotient subspace capacities have distribution
\[
0:1,\ 1:687,\ 2:34664,\ 3:83046,\ 4:138902,\ 5:81540,\ 6:8130,\ 7:61232,\ 8:865.
\]
The peer's cap-distributions for cap $\le3$ and cap $\le5$ match these values.

The saved DFS artifacts are not complete exclusions:

- `dfs_pilot_cap3.json` has `timeout=true` after 90 s and saved 26,967 full depth-19 supports from the explored prefix;
- `cap3_stream_cap48_check.json` has `timeout=true` after 120 s and processed 31,776 cap-$\le3$ supports, all failing later rows;
- `dfs_pilot_cap5.json` has `timeout=true` after 90 s, reached depth 16, and found no full depth-19 support in the explored prefix.

The fact that the generated cap-$\le3$ supports all fail later Wang rows is useful evidence of a strong bottleneck, but it is not a complete Wang-only proof. My canonical recheck of the ten saved cap-$\le3$ supports found many cap-4 violations already, even though the peer stream reported first failures at cap 7; this only means the stream's failure-cap count is tied to row order, not a mathematical minimum.

Core artifact:

- [peer_wang_support_review.json](../../relaxations_and_cuts/results/ghw_singleton_review/peer_wang_support_review.json)

## 4. Rank-21 pool A-bit convention

The peer-reported pool convention bug is real. The rank-21 E11 pool `mod2-rank21a.npy` stores 8-bit core A masks directly in bits 0--7. Applying `CoreQuotient.project9` to these masks incorrectly treats them as 9-bit full A masks and can create zero projected directions.

Independent reconstruction on the first 20 pool rows:

- raw 8-bit masks reconstruct the E11 core on 20/20 rows;
- `CoreQuotient.project9` masks reconstruct it on 0/20 rows;
- row 0 has raw reconstruction difference 0 and projected reconstruction difference 45.

This affects pool-validation sections in scripts that pass pool masks through `project9`; it does not affect canonical Wang-row construction from subspace keys, and it does not affect analysis generalized low-excess pool tests because analysis used raw pool masks.

## 5. Scientific consequence for the active goal

The active rank question remains open: no rank-19 E11 core, no full rank-$\le22$ decomposition, and no rank-$\ge21$ proof has been produced. The strongest reliable progress from earlier analysis is:

1. generalized low-excess contraction geometry is now a sound fixed-A multilist exclusion layer;
2. it gives scalar-clean exclusions in the same-W near-miss family;
3. rank-3 tight sources can strengthen it without changing its mathematical basis;
4. the Wang-support problem has a useful coding-theory interpretation and very strong late-row pressure, but current DFS outputs are still timeout-limited pilots;
5. the pool bit convention has been repaired for future validation work.

The next work should not treat the same-W family or timeout-limited DFS prefixes as global coverage. The valuable path is to build a canonical proof-producing support engine for the distinct nineteen-direction E11 branch, using the complete E11 Wang rows and the sound A-level filters, while preserving a clear bridge to exact fixed-A B/C completion and to the repeated-direction proof already replayed.
