# Corrected Evidence State and Binary Format Audit

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Binary Format Discovery

The peer quotient binaries (`rank2_all_n19.bin`, `rank3_all_n19.bin`) use **E11WANG1 format**:
- 8 bytes: magic `E11WANG1`
- 4 bytes: uint32 row count N
- N × 36 bytes: `<BBHQQQQ` (cap:1B, dim:1B, pad:2B, mask:4×8B=32B)

Total file size: 12 + N × 36.

My Python CEGAR scripts (`branch_cegar.py`) incorrectly treated the files as 
6-byte records (4B mask + 2B cap), reading garbage. The four CEGAR results 
(rank2 branches 1,2,5 and rank3 branch 0) from the wrong parser are **INVALID**.

## Unaffected Evidence

All C++ DFS engines correctly parse E11WANG1 (magic check, 36-byte records). All 
Python filter/export scripts (`filter_e11wang_rows.py`, `export_lift_cut_row.py`,
`transport_lift_cut.py`, `transport_custom_lift_cut.py`) also use correct
E11WANG1 format. Therefore:

### Valid DFS closures:
- Rank-2 branches 4, 6-13: cap≤5 DFS (analysis)
- Rank-2 branch 3: cap≤5 + lift cut DFS (earlier analysis; BUT note review showed lift cuts
  are tautological in branch 3 since it forbids O={1,3,9} and every cut contains ≥1 O-point.
  Branch 3 closure is from quotient occupation + pair propagation only.)
- Rank-3 branches 2-5: cap≤5 DFS (analysis)
- Rank-3 branch 1: cap≤3 DFS with pair propagation (analysis, 584.5s, binary sha ba84c5c1...)

### Valid lift obstructions:
- First 12-point lift-bit obstruction A={9,33,99,160,184,189,192,209,215,224,249,254}
  (analysis, cert sha 9c77e32f...)
- Second 12-point obstruction A={1,3,9,148,160,184,192,198,215,231,249,254}
  (analysis, cert sha 05c7c6e3...)
- Both transported under pivot-17 stabilizer: 48 unique cuts each, 96 total
- Original-row family structure analyses valid (analysis)

## Correct Binary Statistics

| Binary | Rows | cap≤3 | cap≤5 |
|--------|------|-------|-------|
| rank2_all_n19.bin | 417,197 | 162,305 | 360,541 |
| rank3_all_n19.bin | 417,197 | 157,675 | 358,618 |

Cap≤5 for rank2 exactly matches local `rank2_cap5_n19.bin` (360,541 rows).

## review Observation: Support Cut Tautology

All 96 transported support cuts are **automatically satisfied** in rank-2 branches ≥1:
- First orbit: every cut has |cut ∩ O| = 1 (one O-point)
- Second orbit: every cut has |cut ∩ O| = 3 (all three O-points)
- Branches 1-13 forbid all of O={1,3,9}
- With ≥1 absent cut point, max selectable = 11 ≤ 11 = rhs → tautological

Only branch 0 (no forbidden points) has all 96 cuts active.

However, the 1,296 transported relation rows (lift-bit constraints on y0/y1 variables) 
remain nontrivial in ALL branches because they involve points well beyond O.

## Current Open State

| Pivot | Branch | Status | Evidence |
|-------|--------|--------|----------|
| rank2 | 0 | OPEN (lift route) | 2 certified obstructions, not closed |
| rank2 | 1 | OPEN (corrected CEGAR pending) | — |
| rank2 | 2 | OPEN (corrected CEGAR pending) | — |
| rank2 | 3 | CLOSED | quotient+pair DFS |
| rank2 | 4-13 | CLOSED | cap≤5 DFS |
| rank3 | 0 | OPEN (corrected CEGAR pending) | — |
| rank3 | 1 | CLOSED | cap≤3+pair DFS |
| rank3 | 2-5 | CLOSED | cap≤5 DFS |

Corrected CEGAR running: rank2 branches 1,2,5; rank3 branch 0.
