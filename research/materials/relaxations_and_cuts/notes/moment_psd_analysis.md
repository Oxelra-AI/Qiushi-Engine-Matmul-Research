# Moment-Matrix PSD Analysis for E11 Distinct-Support Branch

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Key Finding

The 256×256 moment matrix M constructed from orbit-averaged pair statistics
provides a **global second-moment realizability condition** that is strictly
stronger than the Wang RLT + triangle + block-count constraints tested in
earlier analysis.

For binary x_p ∈ {0,1}, the lifted moment matrix:
- M[0,0] = 1
- M[0,p] = M[p,0] = M[p,p] = x_p  (binary: x²=x)
- M[p,q] = y_{pq}  for distinct p,q

must satisfy M ⪰ 0 for any genuine support.

## Results

### PSD Violations of analysis Witnesses
All four block-count witnesses from analysis violate PSD:

| Witness | n | min eigenvalue | # negative eigenvalues |
|---------|---|---------------|----------------------|
| feasibility_lex | [3,0,0,3,0,13] | -0.1697 | 22 |
| max_omitted | [6,0,11,2,0,0] | -0.1484 | 16 |
| min_omitted | [0,0,0,0,2,17] | -0.0762 | 13 |
| force_zero_omitted | [0,0,0,0,2,17] | -0.1409 | 40 |

This explains why these witnesses failed graph realization in analysis: they are
not even second-moment consistent.

### Uniform Point
The uniform point x_p = 19/255 is exactly PSD (min eigenvalue = 0), confirmed
analytically: the 2×2 block in (e_0, all-ones) has determinant
  1 · (19²/255) - 255 · (19/255)² = 361/255 - 361/255 = 0
and the 254-dimensional complement has eigenvalue x - y = 2242/32385 > 0.

### Implication
PSD alone cannot prove LP infeasibility (uniform point is feasible).
But PSD can exclude specific integer count vectors. The key question is:
**for how many of the 34,335 integer count vectors does LP + PSD have
a feasible point?**

## LP Bug Found and Fixed
The LP builders in orbit_sdp.py and count_vector_scan.py used
NORMALIZED coefficients (dividing by orbit/pair sizes), which:
1. Introduced floating-point precision issues in deduplication (1.5M vs 183K constraints)
2. Were mathematically incorrect (double-normalized)

The fix: match analysis's raw integer coefficients exactly. The corrected script
is `combined_sdp_scan.py`.

## Files
- [moment_psd_check.py](../code/moment_psd_check.py): eigenvalue check
- [moment_psd_check.json](../results/moment_psd/moment_psd_check.json): PSD results for 4 witnesses
- [combined_sdp_scan.py](../code/combined_sdp_scan.py): CORRECTED combined LP+PSD+SDP scan (ready to run)
- [orbit_sdp.py](../code/orbit_sdp.py): BROKEN (wrong LP normalization, timed out)
- [count_vector_scan.py](../../quotient_cores/code/count_vector_scan.py), `fast_count_scan.py`: BROKEN (same issue)
