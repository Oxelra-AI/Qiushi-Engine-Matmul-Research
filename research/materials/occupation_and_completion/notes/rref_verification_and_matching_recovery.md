# LUT RREF Verification — Recovery of 15/38 Matching Closures

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Critical Discovery

The analysis claim that `make_pivot_dict`/`in_span_piv` in `graph_coloring_certificate.py`
was buggy **was itself based on the analysis script's own key-decoding error**, not on a real
membership bug. analysis identified and corrected the key-decoding issue (reading 9-bit chunks
from bit 0 instead of bit 4), but the research memory continued to flag the analysis functions
as affected.

## Verification Result

[verify_lut_rref_and_rerun_strata.py](../../quotient_cores/code/verify_lut_rref_and_rerun_strata.py) tested:

1. **All 8,283,458 LUT keys have RREF bases**: 0 violations. Every basis unpacked from the LUT
   has vectors with distinct highest bits (unique pivots), as guaranteed by construction via
   `rref_basis() → pack_basis() → unpack_basis()`.

2. **`make_pivot_dict`/`in_span_piv` is correct for RREF bases**: 100,000 random (key, point)
   samples compared `in_span_piv` vs `span_of` (full span enumeration): 0 mismatches.

3. **Strata profiles are reproduced**: All 38 matching strata recomputed with the same
   `process_stratum` function show consistent profiles.

## Implication

The analysis `process_stratum` function was **correct all along** because:
- LUT keys store RREF bases by construction
- `unpack_basis(key)` returns these RREF bases
- For RREF bases, `make_pivot_dict` cannot have collisions (each vector has a unique pivot)
- Therefore `in_span_piv` gives correct membership answers
- All downstream vertex exclusions, edge exclusions, and residual computations are correct

## Recovered Matching Closures (15/38)

All DRAT-verified matching strata closures from earlier analysis remain valid:

| k | Closed indices | Method |
|---|----------------|--------|
| 7 | idx32, idx37 | direct negative residual |
| 7 | idx33, idx34 | clique-cover certificates |
| 7 | idx35, idx36 | graph-IS CNF UNSAT + DRAT |
| 6 | idx22, idx23, idx24, idx28 | graph residual-0/1 certificates |
| 6 | idx25 | witness-subset separation DRAT |
| 5 | idx12, idx13, idx14, idx15 | witness-subset separation DRAT |

## Remaining Open Strata (23/38)

| k | Open indices | Survivor counts | Notes |
|---|-------------|-----------------|-------|
| 6 | 26,27,29,30,31 | 252-443 | idx31 is "twin" of closed idx25 |
| 5 | 16,17,18,19,20,21 | 265-448 | idx20 is "twin" of closed idx13/15 |
| 4 | 5,6,7,8,9,10,11 | 275-456 | idx05,09 are "twins" |
| 3 | 2,3,4 | 282-459 | |
| 2 | 1 | 461 | |
| 1 | 0 | 462 | |

"Twin" strata have identical (survivor_count, edge_count) as closed strata,
suggesting graph isomorphism under the larger symmetry group.

## File Evidence

- [results.json](../../quotient_cores/results/lut_verify_and_strata/results.json): full verification and profile data
- [verify_lut_rref_and_rerun_strata.py](../../quotient_cores/code/verify_lut_rref_and_rerun_strata.py): verification script

## Implication for rep2

The rep2 adjacent-pair branch is NOT affected by this recovery. The analysis rep2 evidence
still applies:
- analysis zero-survivor claim is WITHDRAWN (wrong key decoding)
- analysis [1,2,3] prefix closure via DRAT is valid
- analysis ruling-line transport with 95 clauses is valid structure
- rep2 remains open

## Next Steps

1. Close "twin" strata idx20, idx31, idx05, idx09 via witness separation (background task running)
2. Attack remaining open strata by decreasing difficulty
3. For rep2: use the confirmed-correct LUT to build a stronger direct encoding
