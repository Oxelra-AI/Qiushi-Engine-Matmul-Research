# Rep2 Adjacent-Pair Branch Closure & Pivot Bug Discovery

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Critical Finding: Zero Survivors for Prefix {1,2}

The Wang F2 occupation LUT, when scanned with CORRECT span membership
computation, shows that **all 509 candidate projective A-indices are
vertex-excluded for prefix {E₁₁, E₁₂} = {1, 2}** under the rank-20 assumption.

### Evidence
- [summary.json](../results/ruling_line/diagnostic/summary.json): confirms
  `prefix_12_zero_survivors: true`, with 509/509 excluded by lb=18 entries.
- Diagnostic also confirms prefix {1,2,3} has 508/508 excluded (0 survivors).
- Each vertex exclusion is: a LUT entry Φ with lb(Φ)=18, {1,2} ⊂ span(Φ),
  candidate p ∈ span(Φ). With cap = 20-18 = 2 and prefix_occ = 2, residual = 0,
  so p cannot be in ANY rank-20 A-support containing {1,2}.
- Most exclusions come from dim-4 subspaces (493 candidates); 16 come from dim-3.
- Specific verified examples:
  - point 256: key=0x809b103, basis=[259,216,2,1], lb=18, both 1,2 in span
  - point 511: key=0x13d61203, basis=[3,265,245,2], lb=18, both 1,2 in span
  - point 100: key=0x11945003, basis=[3,40,101,2], lb=18, both 1,2 in span

### Mathematical Meaning
No rank-20 A-support over F₂ can contain both E₁₁ and E₁₂. Under the full
GL(3,2)²⋊C₂ group action, this means no rank-20 A-support can contain ANY
adjacent pair of rank-1 matrices. Combined with the verified global cover:
- The adjacent-pair (rep2) branch is EMPTY.
- Every hypothetical rank-20 A-support has ONLY matching-type rank-1 subsets.
- The matching branch (38 strata) is the sole remaining target.

## Bug Discovery: make_pivot_dict / in_span_piv

### Location
[graph_coloring_certificate.py](../../finite_certification/code/graph_coloring_certificate.py), lines 50-62:

```python
def make_pivot_dict(basis):
    return {int(b).bit_length() - 1: int(b) for b in basis if int(b)}

def in_span_piv(piv, v):
    x = int(v)
    while x:
        p = x.bit_length() - 1
        b = piv.get(p)
        if b is None:
            return False
        x ^= b
    return True
```

### Bug
`make_pivot_dict` maps `highest_bit_position → vector`. If two basis vectors
share the same highest bit (i.e., the basis is NOT in row-echelon form), the
later vector OVERWRITES the earlier one. This silently loses a dimension,
causing `in_span_piv` to return False for vectors that ARE in the span.

### Concrete Example
basis = [3, 40, 101, 2] (from LUT key 0x11945003, lb=18)
- 3 = 0b11, highest bit = 1
- 2 = 0b10, highest bit = 1
Both share highest bit 1. make_pivot_dict gives {1: 2, 5: 40, 6: 101}.
Vector 3 is LOST. Now:
- in_span_piv(piv, 1): x=1, p=0, piv[0]=None → FALSE. But 1 = 3^2 IS in span!
- So prefix_occ for {1,2} is UNDERCOUNTED as 1 instead of 2.
- Residual = (20-18)-1 = 1 (edge) instead of correct 0 (vertex exclusion).

### Impact on Previous Results
1. **analysis rep2 marked-orbit profiles**: used `process_rep2` which calls
   `in_span_piv`. The 136 survivors reported for prefix [1,2,3] are WRONG;
   the true count is 0. Similarly for all other marked-orbit profiles.
2. **analysis matching strata**: used `process_stratum` which also calls
   `in_span_piv`. Survivor counts may be overcounted, and some UNKNOWN or
   open strata might close with correct vertex exclusions.
3. **DRAT-verified closures remain valid**: they proved UNSAT for WEAKER
   formulas (with fewer vertex exclusions). Adding more vertex exclusions
   can only strengthen the formula.
4. **Witness-subset learned clauses remain valid**: they are direct consequences
   of Wang rows, not dependent on the pivot computation.

### Fix Required
Replace `make_pivot_dict` / `in_span_piv` with proper Gaussian elimination
that row-reduces the basis before building the pivot dictionary. Or use the
correct `span_of` function (full enumeration) which is verified.

## Ruling-Line Transport (Secondary Finding)

The verified {1,2,3} exclusion transports under group equivariance to all 98
ruling-line triples (left/right rulings of the 7×7 Segre grid). For prefix
{1,2}, this gives 1 unit + 10 binary + 87 ternary clauses. However, the
zero-survivor result makes these clauses REDUNDANT — the base graph alone
closes the rep2 branch without needing ruling-line transport.

The ruling-line observation remains mathematically interesting and may be useful
for other branches or for understanding the structure of rank-20 supports.

## Updated Proof Architecture

Current state toward R_F2(T_<3,3,3>) >= 21:

1. ✅ Wang certificate: R_F2 >= 20
2. ✅ Multiplicity-free: all dim-1 rows have lb=19
3. ✅ No-rank-1-factor exclusion: DRAT verified
4. ✅ Fixed-E11 normalization
5. ✅ **Adjacent-pair (rep2) closure: zero survivors from LUT** ← NEW
6. ⬜ Matching branch: 15/38 strata closed (may improve with bug fix)
7. ⬜ Orbit lift and LUT binding for theorem statement

## Files
- [ruling_line_transport.py](../code/ruling_line_transport.py): ruling-line enumeration
- [verify_zero_survivor.py](../code/verify_zero_survivor.py): diagnostic confirming zero survivors
- [summary.json](../results/ruling_line/diagnostic/summary.json): machine-readable evidence
- [ruling_lines.json](../results/ruling_line/enumerate_test/ruling_lines.json): 98 triples
