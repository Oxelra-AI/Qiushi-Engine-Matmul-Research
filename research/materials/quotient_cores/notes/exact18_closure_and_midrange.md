# exact-18 closure, orbit-symmetrized range probes, and mid-range k status

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Major result: exact k=18 branch completely closed

The background task `s13_t36_tool1` completed: all 62 remaining exact-18 high-pair
orbits (indices 7–68) received DRAT-verified proof certificates.  Combined with the
7 earlier verified pairs (indices 0–6), all 69 exact-18 pair orbits are now verified.

Summary:
- 66 closed with max-intersection-size ≤ 7 filtered rows
- 3 needed max-intersection-size ≤ 9 (pair indices 2 = (17,26), 28 = (20,38), 65 = (160,304))
- 0 missing proofs

Exact-18 proof artifacts span:
- `workspace/data/rank1_fixed_high_filtered_cnf/pair_000_*` through `pair_004_*`
- `workspace/data/rank1_pair_filtered_proof_batch/pilot_005_006/`
- `workspace/data/rank1_pair_filtered_proof_batch/batch_007_068/`

Combined with the single-high exclusions (orbits 10, 84, 161), this means:

> **Theorem component (exact k=18):** Under the expanded Wang occupation LUT, no
> fixed-E11 length-20 Wang-admissible A-support over F2 can have exactly 18
> rank-1 A-factors and exactly 2 higher-rank A-factors.  This is verified by 3
> single-high DRAT proofs and 69 high-pair DRAT proofs, covering all Stab(E11)
> orbits via the partition certificate.

## Orbit-symmetrized range solver: rep2 and rep16

Built [wang_fixed_e11_symm_range_cpsat.py](../code/wang_fixed_e11_symm_range_cpsat.py) which computes the
joint stabilizer Stab(E11, rep), orbit-closes violation seed rows, and adds
lex-leader symmetry breaking.

### Rep 2 (Stab size 96, 95 lex constraints)
- **No seeds**: OPTIMAL in 213s, rank histogram {1:16, 2:2, 3:2}, full-LUT scan: 547 violations
- **Seed from first violation set (201 → 1,212 orbit-closed)**: UNKNOWN after 600s
- **Combined seeds (394 → 11,040 orbit-closed)**: UNKNOWN after 576s

### Rep 16 (Stab size 32, 31 lex constraints)
- **Seed from violation set (200 → 2,796 orbit-closed)**: UNKNOWN after 600s

**Conclusion:** Orbit-closure and lex-leader breaking reduce the symmetry but do not
close rep2/rep16 within 600s.  The solver finds lex-minimal supports that still violate
hundreds of full-LUT rows; adding those rows orbit-closed pushes the model to UNKNOWN
rather than INFEASIBLE.

## Compact rep10 attempt

Rep10 with k=1..17 was already CP-SAT INFEASIBLE using dims 1-3 + through-fixed 4-8
+ rank-1 projection.  The DIMACS replay is 6.6M variables / 40.6M clauses and did not
solve in 900s.

Tested: dims 1-3 + through-dim-6 only + rank-1 projection (no dims 4,5,7,8 through
fixed).  Result: UNKNOWN after 600s.  So through-dim-6 alone is not sufficient at 600s;
the full through-4-8 family is needed for CP-SAT closure, and the resulting CNF is too
large for CaDiCaL.

## Current proof tree state

### Closed branches (all DRAT-verified):
1. No rank-1 A-factor (all-rank-3 and rank-2-or-3 branches)
2. Fixed-E11, second-point reps 17, 20, 84, 160, 161
3. **Fixed-E11, exact k=18** (just completed this ARTIFACT)

### Open branches (k=1..17 range within fixed-E11):
4. Rep 2: CP-SAT OPTIMAL with full-LUT violations; orbit-closed seeding → UNKNOWN
5. Rep 10: CP-SAT INFEASIBLE but DIMACS too large for DRAT
6. Rep 16: CP-SAT OPTIMAL with full-LUT violations; orbit-closed seeding → UNKNOWN

### Remaining work for R_F2(T333) ≥ 21:
- Close reps 2, 10, 16 for k=1..17 with verified proof objects
- Either find a compact enough CNF that CaDiCaL can handle, OR
- Raise Wang table entries on the specific weak subspaces identified by the violations

## Violation analysis: where Wang's table is weakest

Rep2 violations (547 total): concentrated in dims 5-6 at lb=15, with some in dim 7 at lb=12.
The worst violations have excess 2, meaning the support uses 7 points in a cap-5 subspace.

Rep16 violations (555 total): similar pattern, concentrated in dims 5-6 at lb=15 and
dim 7 at lb=12.  The dim-8 violation at lb=9 with excess 2 hits the full 256-point
ambient space.

These violations identify specific restriction subspaces where Wang's backtracking
search hit its 10,000,000-ARTIFACT limit.  Raising even a few of these lb=15 entries to 16
(or lb=12 to 13) would change the cap and potentially make the residual system
unsatisfiable.  This is the "raise the table" approach suggested by the review.

## Related Mathematical Checks

Related characteristic-zero studies examine symmetry-quotient analysis,
projected kernel models, and semisimple weight blocks.  An F2
rank ≥ 21 increment would not alone solve the char-zero endpoint.  The fixed-A B/C
solver remains available for any full-LUT E11 support.

The exact-18 closure does not decide the remaining k=1..17 cases.
