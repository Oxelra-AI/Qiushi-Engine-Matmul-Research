# Key Findings

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## 1. Conflict Graph Analysis (cap-1 rows)
- Rank-2 quotient: alpha(G) = 54 (cap-1 conflict graph, 18,642 edges, density 0.576)
- Rank-3 quotient: alpha(G) = 54 (17,286 edges, density 0.534)
- Cap-1 rows alone cannot close either quotient (alpha >> 19)

## 2. CEGAR CP-SAT Results
- **Rank-2**: Found fully Wang-admissible 19-support in 3 rounds, 69s:
  `[1, 3, 9, 33, 99, 128, 132, 144, 148, 160, 184, 189, 192, 198, 209, 215, 224, 249, 254]`
  Verified against all 417,197 Wang rows: **0 violations**
- **Rank-3**: CEGAR stalled at round 2 (UNKNOWN after 111s, 5,482 conflicts)
  Rounds 0-1 found solutions with 123 and 111 violations respectively.

## 3. Fixed-A Brent Completion (rank-2 admissible support)
- CNF: 6,336 vars, 23,085 clauses
- **CaDiCaL: UNSATISFIABLE** in 943.6s, 13,054,975 conflicts
- The Wang-admissible support has NO valid B/C completion
- Wang admissibility is necessary but NOT sufficient for decomposability

## Implications
1. **Wang occupation alone cannot close the rank-2 quotient** — Wang-admissible supports exist
2. **But at least one admissible support fails Brent completion** — the gap matters
3. The constructive question: do ANY Wang-admissible supports have valid completions?
4. The lower-bound question: does the combination of Wang + Brent exclude all rank-19 quotient decompositions?
5. Need to enumerate and test more Wang-admissible supports
6. E11 with all 417k rows: CP-SAT returned UNKNOWN after 242s (hard to solve directly)
