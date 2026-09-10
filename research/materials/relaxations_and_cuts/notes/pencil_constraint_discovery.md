# Dual-Line Pencil Constraint — A New B/C Compatibility Mechanism

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Discovery

For a dual line D = span(q₁, q₂) in F₂⁸ (the E11 quotient A-space), each
A-direction p gets a color (q₁(p), q₂(p)) ∈ {00, 10, 01, 11}. In any actual
tensor decomposition, the color-class term sums must satisfy:

    L(q₁) = X₁₀ + X₁₁,    rank(X₁₀) ≤ c₁₀
    L(q₂) = X₀₁ + X₁₁,    rank(X₀₁) ≤ c₀₁
                              rank(X₁₁) ≤ c₁₁

where c_v counts the number of support points (= terms, in the distinct branch)
in color class v. Setting Z = X₁₁, the **pencil realizability** question is:

> Does there exist a 9×9 matrix Z over F₂ with
>   rank(Z) ≤ c₁₁,  rank(M₁+Z) ≤ c₁₀,  rank(M₂+Z) ≤ c₀₁?

The individual contraction bounds only require:
- c₁₀ + c₁₁ ≥ rank(L(q₁))
- c₀₁ + c₁₁ ≥ rank(L(q₂))
- c₁₀ + c₀₁ ≥ rank(L(q₁+q₂))

These are *necessary* but *not sufficient* for pencil realizability.

## Normalization (both M₁, M₂ invertible)

When both contractions have rank 9, set W = M₁⁻¹Z. The conditions become:
- rank(W) ≤ c₁₁
- rank(I + W) ≤ c₁₀
- rank(A + W) ≤ c₀₁  where A = M₁⁻¹M₂

Via Sylvester's identity, parametrizing Z = UV^T (U, V are 9×c₁₁, rank c₁₁):
- corank(M₁ + UV^T) = dim ker(I_{c₁₁} + V^T M₁⁻¹ U)
- corank(M₂ + UV^T) = dim ker(I_{c₁₁} + V^T M₂⁻¹ U)

For the "tight" case where corank must equal c₁₁:
V^T M_i⁻¹ U = I_{c₁₁}, yielding a LINEAR system in V for fixed U.

## Computational Results

### cn122 positive control
- 21 core terms, 18 unique A-directions (3 directions have multiplicity 2)
- With correct TERM-based color counts: **192/192 rank-9 lines pass pencil**
- With incorrect DIRECTION-based counts: all 192 fail (wrong budget!)
- The actual term matrices X_{11} satisfy all rank constraints

### Near-miss support S = [1,2,3,4,8,20,24,31,32,36,64,73,109,127,128,141,160,182,219]
- 19 distinct directions, each appearing once → direction counts = term counts
- **All 10,795 dual lines pass individual contraction bounds** (ib_fail = 0)
- **106/192 all-rank-9 lines are pencil-INFEASIBLE** (55%)
- The 9 violated Wang rows are NOT detected by individual dual-line contraction bounds
- The pencil captures structure that BOTH individual contraction bounds and specific
  Wang rows miss about B/C compatibility

### Detailed infeasible cases
| Line | Colors (c₀₀,c₁₀,c₀₁,c₁₁) | Target | Best found | Gap |
|------|---------------------------|--------|------------|-----|
| [42,149,191] | (3,3,6,7) | rank(M1+Z)≤3 | 6 | 3 |
| [55,141,186] | (3,3,6,7) | rank(M1+Z)≤3 | 7 | 4 |
| [78,185,247] | (3,5,5,6) | both ≤5 | (5,6) | 1 |

50,000 random trials per case; consistent with analytical one-side-tight tests
(500 U-trials × exhaustive/large-sample V per U).

### Infeasible color profiles
Many infeasible profiles have c₁₁ ≥ 5 (large overlap class), c₀₀ ≤ 3
(few kernel points), and all three contractions of rank 9. The infeasibility
depends on the SPECIFIC matrices (M₁, M₂), not just the budget triple:
profile (2,6,7,4) is infeasible for 2 lines and feasible for 3.

## Scientific Significance

1. **New constraint type**: The pencil test is strictly stronger than individual
   contraction bounds for 106/192 = 55% of all-rank-9 dual lines on the near-miss.

2. **B/C compatibility**: Unlike Wang occupation (A-only) and individual contraction
   bounds (single-functional), the pencil captures SIMULTANEOUS B/C term-matrix
   compatibility across a dual line. The "shared Z" structure cannot be decomposed
   into individual rank checks.

3. **Potential for Wang-admissible rejection**: If a support passes all 417,198
   Wang rows but fails a pencil constraint, that would be a genuinely new obstruction
   for the distinct E11-core problem, complementary to existing Wang occupation.

4. **Efficient evaluation**: For any candidate support, the pencil test on all 192
   rank-9 lines is O(192 × polynomial in 9), much cheaper than full B/C completion.

## Open Questions

1. Can the pencil reject Wang-admissible distinct 19-point supports?
2. What is the complete "infeasible pencil region" for each dual line (all
   forbidden (c₁₀, c₀₁, c₁₁) triples)?
3. Can the pencil constraints be integrated into CP-SAT as derived cuts?
4. Do the 6,588 mixed-rank (9,6,*) or (9,3,*) lines also contribute?
5. Is there a compact algebraic characterization of pencil infeasibility
   in terms of the invariant factors of A = M₁⁻¹M₂?

## Key Files
- [pencil_pilot.py](../code/pencil_pilot.py): initial enumeration and random search
- [analytical_pencil.py](../code/analytical_pencil.py): analytical one-side-tight test
- [pencil_validation.py](../code/pencil_validation.py): cn122 validation (found bug)
- [cn122_fix_and_detail.py](../../exact_baselines/code/cn122_fix_and_detail.py): fixed validation + detailed cases
- [pencil_pilot_results.json](../results/pencil_pilot/pencil_pilot_results.json): initial survey
- [analytical_pencil_results.json](../results/pencil_pilot/analytical_pencil_results.json): full 192-line results
- [pencil_cn122_fix_and_detail.json](../../exact_baselines/results/pencil_pilot/pencil_cn122_fix_and_detail.json): fixed cn122 + detail

## Limitations
- The 106 infeasibilities are empirical (random search + analytical), not SAT-proven.
  For a proof, each would need a deterministic infeasibility certificate.
- The pencil is a NECESSARY condition for decomposition, not sufficient.
  A pencil-feasible support might still fail full B/C completion.
- These results are for F₂ and the E11 core; they do not directly apply to
  characteristic-zero rank questions.
