# exact exchange-neighborhood repair around the trace-consistent 9-violation support

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Starting support

The target support is the analysis augmented-certificate separator support

```text
S = [1,2,3,4,8,20,24,31,32,36,64,73,109,127,128,141,160,182,219].
```

It has 19 distinct E11 quotient directions. Exact evaluation in
[aug_separator_support_trace_evaluation.json](../../occupation_and_completion/results/trace_dependency_cuts/aug_separator_support_trace_evaluation.json)
showed:

- 9 complete Wang violations, all `L=12`, excess 1;
- 6 violating rows of core dimension 5 and 3 of core dimension 6;
- passes zero-domain, linear membership, transversality, size-2 quotient-rank, local odd trace-dependency, compressed corrected-trace, and full corrected-trace tests.

Thus its remaining known obstruction is complete Wang occupation, not the corrected trace relaxation.

## Exact exchange-neighborhood model

For an exchange radius `d`, require a new support `S'` to satisfy

```text
|S'| = 19,  |S ∩ S'| >= 19-d.
```

For a Wang row `U` with capacity `cap = 19-L(U)`, the occupancy in a `d`-exchange neighborhood can increase by at most `d`. Therefore if

```text
slack_S(U) = cap - |S ∩ U| >= d,
```

then `U` cannot become violated anywhere in that neighborhood. The filtered model keeping exactly the rows with `slack_S(U) < d` is therefore equivalent to the complete Wang table inside the radius-`d` neighborhood. This is still only an A-support necessary-condition model, not a B/C decomposition.

Script:

- [neighborhood_repair.py](../code/neighborhood_repair.py)

Data directory:

- `workspace/data/neighborhood_repair/`

Slack profile around `S`:

```text
slack -1:       9 rows   (the nine current violations)
slack  0:    1114 rows
slack  1:   17948 rows
slack  2:  107643 rows
slack  3:  154850 rows
slack  4:   96075 rows
slack  5:   27533 rows
slack  6:    9431 rows
slack  7:    2146 rows
slack  8:     376 rows
slack  9:      68 rows
slack 10:       5 rows
```

Consequent exact filtered row counts:

```text
d=1:   1,123 rows
d=2:  19,071 rows
d=3: 126,714 rows
d=4: 281,564 rows
d=5: 377,639 rows
d=6: 405,172 rows
```

## CP-SAT outcomes for pure complete-Wang local repair

To isolate the occupation obstruction, the main runs disabled the contraction lower bounds; adding them can only make these neighborhoods harder.

| radius | filtered rows | result | file |
|---:|---:|---|---|
| 1 | 1,123 | INFEASIBLE in 0.044 s | `repair_d1_wang_only_120s.json` |
| 2 | 19,071 | INFEASIBLE in 5.479 s | `repair_d2_wang_only_120s.json` |
| 3 | 126,714 | INFEASIBLE in 21.322 s | `repair_d3_wang_only_300s.json` |
| 4 | 281,564 | INFEASIBLE in 45.204 s | `repair_d4_wang_only_600s.json` |
| 5 | 377,639 | INFEASIBLE in 176.287 s | `repair_d5_wang_only_900s.json` |
| 6 | 405,172 | UNKNOWN after 900 s | `repair_d6_wang_only_900s.json` |

Interpretation: the nine excess-one Wang violations are not repaired by any support within five exchanges of `S`. The first unresolved radius in this exact local model is `d=6`. This does not exclude the distinct branch globally; it says that if a complete-Wang-admissible support exists, it is at distance at least six from this near-miss, unless the CP-SAT `d=6` run later finds one.

## Proof-producing local occupation certificates

Script:

- [local_repair_cnf.py](../code/local_repair_cnf.py)

The CNF encodes exactly the same pure Wang radius-`d` local model: 255 point variables, exact length 19, the radius constraint, and all complete-table rows with `slack_S(U)<d`. No contraction or trace cuts are included.

Certified results obtained in this ARTIFACT:

### Radius 2

- CNF: `workspace/data/neighborhood_repair/cnf/current_support_repair_d2.cnf`
- metadata: [current_support_repair_d2.meta.json](../../occupation_and_completion/results/neighborhood_repair/cnf/current_support_repair_d2.meta.json)
- status: [current_support_repair_d2.status.json](../../occupation_and_completion/results/neighborhood_repair/cnf/current_support_repair_d2.status.json)
- variables: 1,075,763
- clauses: 2,300,926
- row count: 19,071
- CNF SHA256: `187ae7171e15e49537a9e14d7914a5e24b8068bac85fab18248f87bfa90aa4e9`
- DRAT SHA256: `9cdf1dab30a1009829dff8253c5c018dc054767648c1619dc08142afbcb0fc59`
- CaDiCaL exit 20 in 21.617 s; `drat-trim` exit 0 with `s VERIFIED` in 11.603 s.

### Radius 3

- CNF: `workspace/data/neighborhood_repair/cnf/current_support_repair_d3.cnf`
- metadata: [current_support_repair_d3.meta.json](../../occupation_and_completion/results/neighborhood_repair/cnf/current_support_repair_d3.meta.json)
- status: [current_support_repair_d3.status.json](../../occupation_and_completion/results/neighborhood_repair/cnf/current_support_repair_d3.status.json)
- variables: 5,537,327
- clauses: 11,872,994
- row count: 126,714
- CNF SHA256: `a2cfc55f4e3faf27291bb3631de8f73de3a71a528d3af1639238bbbdcdae74b9`
- DRAT SHA256: `21e1d03b0f109fcab8d33b8eb2bcfe681e8dde7eecd8ee5b043fb380e65e6f9f`
- CaDiCaL exit 20 in 158.312 s; `drat-trim` exit 0 with `s VERIFIED` in 208.044 s.

A radius-4 CNF/DRAT run was submitted as managed background task `s54_t23_tool1` with target `workspace/data/neighborhood_repair/cnf/current_support_repair_d4.cnf`. Do not use it until the runtime delivers its result.

## Guarded trace-certificate reporting repair

The analysis script `trace_certificate_cuts.py` cross-applied certificate consequences to stored supports without checking whether the target support saturated every contraction in the certificate guard set. This affected only the reporting phrase about cross-coverage, not the CP-SAT models, which encoded guards.

Repair script:

- [guarded_certificate_coverage.py](../../finite_certification/code/guarded_certificate_coverage.py)

Repair output:

- [guarded_trace_certificate_coverage.json](../../finite_certification/results/neighborhood_repair/guarded_trace_certificate_coverage.json)

With the 17 augmented certificates and 23 deduplicated stored targets, the guarded recomputation finds:

- targets with at least one active certificate: 15/23;
- targets hit by a guarded certificate consequence: 15/23;
- targets hit by local inconsistent direction: 3/23;
- targets hit by pure parity under active guard and no selected free/inconsistent directions: 12/23.

So the previous wording that all stored supports were hit is withdrawn. The corrected statement is that many stored Wang-inadmissible near-misses are hit by their own or other active guarded certificates, but broader coverage is not established.

## Background trace-plus-size5 separator result

The managed analysis task `s53_t51_tool1` delivered during analysis. It ran the augmented 17 certificate packages plus all 216,576 size-5 local odd-dependency cuts starting from the `L>=15` model. It returned `UNKNOWN` in round 0 after 601.332 s, without producing a support:

- result JSON: [separator_L15_augcert_size5_4r_600s.json](../results/trace_dependency_cuts/separator_L15_augcert_size5_4r_600s.json)
- task result: `workspace/tasks/s53_t51_tool1/result.json`

This does not exclude anything. It supports the interpretation that the trace layer should remain as conditional search restrictions, while the current trace-consistent near-miss is blocked only by Wang occupation.

## Scientific interpretation

The exact local repair experiment gives a clean new fact about the best current trace-consistent near-miss: its nine `L=12` occupation violations cannot be repaired by small edits. Radius 5 is already a large local neighborhood, and pure Wang occupation alone closes it computationally; radii 2 and 3 are backed by replayed DRAT certificates, while radius 4 proof production is still pending. Radius 6 becomes close to the full table and was not resolved by the 900 s CP-SAT run.

This shifts the research lesson away from adding more trace certificates for this support: no corrected trace consequence presently separates it. The next valuable work should either turn the local Wang obstruction into a more structural low-slack occupation explanation, or return to global support search/proof production with the knowledge that admissible supports, if they exist, are not small repairs of this near-miss.
