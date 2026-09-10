# uniform LP obstruction, verified new face cuts, and proof-core recurrence

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Context

analysis proved a complete-Wang support-face cut for the 65-point positive support `J` of the saved analysis fractional LP point: no distinct 19-point E11 support contained in `J` satisfies the complete 417,199-row E11 Wang table, hence every complete-Wang distinct support satisfies `sum_{p in J} x_p <= 18`. analysis transported that cut under the 1,152 checked E11 stabilizer maps and found new fractional LP supports of sizes 71 and 65 whose own face models were CP-SAT infeasible.

The analysis review note emphasized an important separation: small support-face cuts can be valid learned clauses for the integer support problem, but they cannot by themselves give an LP infeasibility proof, because the diffuse uniform point survives all such cuts.

## 1. Exact uniform point check

Script:

- [uniform_cut_reach.py](../code/uniform_cut_reach.py)

Output:

- [uniform_cut_reach.json](../results/uniform_reach/uniform_cut_reach.json)

I checked the point

```text
x_p = 19/255  for all 255 nonzero E11 quotient directions p.
```

The calculation uses exact rational arithmetic. It verifies:

- total mass is exactly 19;
- every complete E11 Wang row is satisfied: `uniform_violations_count = 0`;
- for dimensions d=1,...,7, the minimum recorded capacities are
  `1, 1, 2, 3, 3, 5, 10`, while the uniform occupancies are
  `19(2^d-1)/255`;
- the smallest nontrivial Wang slack occurs among dim-6 L=14 rows and is `26/85` (the zero and full-space equations are tight in the harmless sense expected from cardinality);
- any cut of the form `sum_{p in J} x_p <= 18` is satisfied by the uniform point whenever `|J| <= floor(18*255/19) = 241`.

Consequences for current cuts:

- each transported J65 cut has uniform left-hand side `247/51 ≈ 4.843`, far below 18;
- a size-71 face cut has uniform left-hand side `1349/255 ≈ 5.290`, far below 18;
- the analysis radius-3 overlap cut on a 19-set has uniform left-hand side `361/255 ≈ 1.416`, far below 15.

This is a structural reason not to run a pure LP convergence loop based only on small face cuts. These cuts remain sound and useful for integer proof search, but an LP contradiction would require different inequalities that cut diffuse feasible configurations such as the uniform point.

## 2. Two new complete-Wang support-face proofs

Script:

- [general_face_cnf.py](../code/general_face_cnf.py)

Compact records:

- [transJ65_random630631_cut_record.json](../results/face_cnf/transJ65_random630631_cut_record.json)
- [transJ65_random630632_cut_record.json](../results/face_cnf/transJ65_random630632_cut_record.json)
- manifest [face_cut_records_manifest.json](../results/face_cnf/face_cut_records_manifest.json)

### Face from random seed 630631

This is the size-71 positive support of run 1 in [lp_with_transported_J65_cuts.json](../results/j65_transport/lp_with_transported_J65_cuts.json).

Proof files:

- CNF: `workspace/data/face_cnf/transJ65_random630631.cnf`
- CNF SHA256: `d9e83ca246234cfa6f3c10b7c51a0154d5c7bf15244aaa5e9c6245c61635ca54`
- DRAT: `workspace/data/face_cnf/transJ65_random630631.drat`
- DRAT SHA256: `7e08f9406db6072ca7f7d32e6a97272c378a444eb77020f927db951f4f99d97e`
- status: [transJ65_random630631.status.json](../results/face_cnf/transJ65_random630631.status.json)
- meta: [transJ65_random630631.meta.json](../results/face_cnf/transJ65_random630631.meta.json)
- extracted input core: `workspace/data/face_cnf/transJ65_random630631.input_core.cnf`

Encoding/proof summary:

- primary variables: 71;
- final variables: 2,697,267;
- clauses: 5,284,109;
- raw complete-Wang rows relevant on the face: 174,714;
- unique restricted constraints after exact deduplication: 166,795;
- CaDiCaL returned UNSAT in 638.474 s;
- `drat-trim` returned VERIFIED in 633.012 s;
- input core contains 88,720 input clauses.

The proven support consequence is

```text
sum_{p in J_630631} x_p <= 18.
```

### Face from random seed 630632

This is the size-65 positive support of run 2 in [lp_with_transported_J65_cuts.json](../results/j65_transport/lp_with_transported_J65_cuts.json).

Proof files:

- CNF: `workspace/data/face_cnf/transJ65_random630632.cnf`
- CNF SHA256: `48116be693e379ac772ec7f8cd3e2dfedb3018c25bde69c90b865f280c0c88d6`
- DRAT: `workspace/data/face_cnf/transJ65_random630632.drat`
- DRAT SHA256: `8e0350833af9b10229640c88adaf4b882bda04fe6744a5366c6b631a7be40f06`
- status: [transJ65_random630632.status.json](../results/face_cnf/transJ65_random630632.status.json)
- meta: [transJ65_random630632.meta.json](../results/face_cnf/transJ65_random630632.meta.json)
- extracted input core: `workspace/data/face_cnf/transJ65_random630632.input_core.cnf`

Encoding/proof summary:

- primary variables: 65;
- final variables: 2,069,890;
- clauses: 4,033,097;
- raw complete-Wang rows relevant on the face: 147,575;
- unique restricted constraints after exact deduplication: 139,271;
- CaDiCaL returned UNSAT in 158.392 s;
- `drat-trim` returned VERIFIED in 274.704 s;
- input core contains 41,959 input clauses.

The proven support consequence is

```text
sum_{p in J_630632} x_p <= 18.
```

Both consequences are complete-Wang A-support cuts over the E11 quotient in characteristic 2. They do not prove global distinct-branch infeasibility and do not say anything about B/C completion or characteristic-zero rank.

## 3. Mapping and comparing input cores

Scripts:

- [analyze_face_core.py](../code/analyze_face_core.py)
- [compare_face_cores.py](../code/compare_face_cores.py)

Outputs:

- [transJ65_random630631_core_clause_analysis.json](../results/face_core/transJ65_random630631_core_clause_analysis.json)
- `workspace/data/face_core/transJ65_random630631_used_constraints.pkl/jsonl`
- [transJ65_random630632_core_clause_analysis.json](../results/face_core/transJ65_random630632_core_clause_analysis.json)
- `workspace/data/face_core/transJ65_random630632_used_constraints.pkl/jsonl`
- [face_core_recurrence_summary.json](../results/face_core/face_core_recurrence_summary.json)
- [core_row_cross_tests.json](../results/face_core/core_row_cross_tests.json)

The face-core mapping matched every extracted input-core clause for both new proofs.

Used representative full Wang rows:

| face | J size | input-core clauses | used representative full rows |
|---|---:|---:|---:|
| original J65 (analysis analysis) | 65 | 38,800 | 9,469 |
| random630631 | 71 | 88,720 | 16,127 |
| random630632 | 65 | 41,959 | 9,645 |

Across the three proofs:

- union of representative row IDs: 30,821;
- rows used in exactly one proof: 26,798;
- rows used in at least two proofs: 4,023;
- rows used in all three proofs: 397.

Recurring rows are not confined to a single L layer. Among rows recurring in at least two proofs, the L-distribution is:

```text
L=3: 16, L=6: 98, L=9: 240, L=11: 2, L=12: 404,
L=13: 14, L=14: 89, L=15: 754, L=16: 296, L=17: 2105, L=18: 5.
```

The all-three intersection is much smaller and also mixed:

```text
L=3: 8, L=6: 19, L=9: 21, L=12: 23, L=14: 4,
L=15: 110, L=16: 7, L=17: 205.
```

This suggests some recurring low-dimensional/high-L pressure, especially L=17 rows, but not a clean single-row-type theorem. The extracted row sets are proof/encoding dependent and should be used as hypotheses or small-row subsets to test, not as mathematical structure by themselves.

## 4. Cross-tests of proof-core row sets

Script:

- [core_row_cross_tests.py](../code/core_row_cross_tests.py)

Output:

- [core_row_cross_tests.json](../results/face_core/core_row_cross_tests.json)

The CP-SAT cross-tests restricted each proof-core row set to each of the three faces, with a short 20 s budget per test. These are exploratory statuses unless later replayed as CNF/DRAT.

Observed pattern:

- the 397-row all-three intersection is too weak: it gives OPTIMAL supports on all three faces, with 1,114–1,744 complete-Wang violations after full rescan;
- the 4,023-row recurring-at-least-two set excludes the two 65-faces in the short test and is UNKNOWN on the 71-face;
- the 30,821-row union excludes all three faces in the short test;
- the random630631 proof-core row set (16,127 rows) excludes all three faces in the short test;
- pairwise intersections are mixed: some exclude the corresponding face, others permit supports with hundreds to thousands of complete-Wang violations.

This supports the idea that proof-core rows have reusable pressure, but the direct intersection is too weak and the reusable mechanism is not yet distilled. A productive next computation would be a proof-producing minimization or PB/CNF replay around the random630631 core-row set, not merely more arbitrary face cuts.

## 5. Transported family of three verified faces

Script:

- [transport_face_families_search.py](../code/transport_face_families_search.py)

Outputs:

- `workspace/data/transported_faces/transported_face_families.json`
- [cpsat_reduced_faces_overlap_300s.json](../results/transported_faces/cpsat_reduced_faces_overlap_300s.json)

The three verified base faces each have 1,152 distinct stabilizer images. The union has 3,456 distinct cuts; there are no duplicate images between the three base families.

Union family summary:

- union cut count: 3,456;
- image sizes: 65 and 71;
- union family SHA256: `b8682112f1f1d973d91e2530435c8fdb704cbf39d0f57f46a06337410343ed02`;
- point-frequency histogram across all 3,456 images:
  - 9 points appear in 256 cuts;
  - 72 points appear in 736 cuts;
  - 96 points appear in 852 cuts;
  - 36 points appear in 1,088 cuts;
  - 36 points appear in 1,280 cuts;
  - 6 points appear in 1,536 cuts.

Known stored near-miss supports from analysis have maximum overlap only 13 or 14 with these transported face cuts, so this family does not simply cover the old sampled near-miss set.

A CP-SAT search using the primitive-reduced 320,366-row Wang formulation, the 3,456 transported face cuts, and the 1,152 transported radius-3 overlap cuts returned UNKNOWN after about 301 s solving:

- output: [cpsat_reduced_faces_overlap_300s.json](../results/transported_faces/cpsat_reduced_faces_overlap_300s.json);
- row source: `primitive_reduced_key_filter`;
- Wang rows added after trivial skips: 319,583;
- transported face cuts: 3,456;
- transported overlap cuts: 1,152;
- status: UNKNOWN.

This produced neither a support nor an impossibility proof.

## 6. related analysis record recorded separately

related analysis analysis reports a characteristic-zero transpose-layer correction and new route:

- the correct first slice space L1 has basis B_ab with entries at `(3b+k, 3k+a)`, not `{X tensor I_3}`;
- tau-invariant decomposition reduces to `L1 subset span{v_l w_l^T}` with u-coefficients determined linearly;
- Burichenko's Laderman automorphism contains a tau-type involution, giving a rank-23 occupied transpose layer with skeleton `(f=7,m=8,N=15)`;
- related analysis is running GF(3) systematic search.

I read `notes/unified_containment_synthesis.md` and key data files enough to confirm the content to be preserved as a separate characteristic-zero line. It must not be mixed with the F2 E11 occupation statements above.

## Research meaning after analysis

The execution line is stronger in two ways:

1. Two more support-face cuts are now theorem-level complete-Wang consequences with replayable CNF/DRAT proofs.
2. The uniform point exactly demonstrates that serial small-face exclusions cannot be an LP-infeasibility strategy; the face cuts should be treated as learned clauses and proof-core samples for the integer support problem.

The unresolved core remains: no complete-Wang-admissible distinct 19-point E11 support has been found or ruled out globally. If a support is found, it still needs the full fixed-A B/C compatibility and exact reconstruction pipeline. If exclusion is the route, it must become a replayable global SAT/PB/DRAT/VeriPB proof or a mathematical argument, not an accumulation of LP-face exclusions.
