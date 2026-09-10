# analysis sequential-counter error and restoration of the open branch status

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Main conclusion

The analysis assertion `R_F2(T_<3,3,3>) >= 21` is not established.  The three new proof objects for fixed-E11 representatives 2, 10, and 16 were produced from an invalid CNF encoding.  The remaining fixed-E11 mid-range branches therefore stay open exactly as they were at the end of analysis / analysis, except that we now understand one concrete encoding trap to avoid.

## Error mechanism

[wang_rep10_seqcnt_proof.py](../../quotient_cores/code/wang_rep10_seqcnt_proof.py) encoded the global equality on the decision variables as

```python
for card in [CardEnc.atmost(dp_lits, target, top_id=top, encoding=EncType.seqcounter),
             CardEnc.atleast(dp_lits, target, top_id=top, encoding=EncType.seqcounter)]:
    top = max(top, card.nv)
    ...
```

Python constructs both `CardEnc` objects before the loop body updates `top`.  Thus the at-most and at-least sequential-counter circuits receive the same auxiliary-variable interval.  These two unrelated auxiliary meanings are forced to share variables, producing an artificial contradiction before any Wang row is used.

The isolated reproduction is in [seqcounter_global_cardinality_audit.py](../code/seqcounter_global_cardinality_audit.py) with outputs under `workspace/data/audit/`:

- `global_equal_buggy_shared_top.cnf`: only the analysis-style global equality for 509 decision variables and target 18.  CaDiCaL returns UNSAT in 0.096 s; DRAT size 21 bytes; DRAT SHA256 `da85dff6036cac12fd427db98f2c35e6613339dae6ccba3fdafcbeeea2ba277f`.
- `global_equal_correct_disjoint_aux.cnf`: the same equality with disjoint auxiliary ranges, created by updating `top` after the at-most encoder before constructing the at-least encoder.  CaDiCaL returns SAT.

The 21-byte DRAT hash is identical to the DRAT hash in all three analysis branch directories.  The core extracted from the analysis rep2 formula is identical, clause-for-clause after the header, to the core of the isolated buggy global equality:

- `workspace/data/audit/rep2_core.cnf`
- `workspace/data/audit/global_equal_buggy_shared_top_core.cnf`

A direct comparison printed:

```text
{'rep_core_clauses': 153, 'bug_core_clauses': 153, 'bodies_identical': True,
 'rep_header': 'p cnf 3866597 153', 'bug_header': 'p cnf 9347 153'}
```

Therefore the analysis DRAT proofs certify only the inconsistent global-cardinality subencoding, not the Wang occupation problem.

## Direct mathematical cross-check against previous witnesses

The analysis / analysis rep2 and rep16 CP-SAT supports were evaluated directly against the mathematical row subset that analysis intended to encode: all one-dimensional Wang rows plus dimension 4 and dimension 6 Wang rows containing the fixed prefix `[E11, rep]`.  This check does not use SAT auxiliary variables.

Script: [intended_subset_check.py](../../quotient_cores/code/intended_subset_check.py).
Outputs:

- [rep2_support_vs_intended_dim1_through46.json](../../occupation_and_completion/results/audit/rep2_support_vs_intended_dim1_through46.json)
- [rep16_support_vs_intended_dim1_through46.json](../../occupation_and_completion/results/audit/rep16_support_vs_intended_dim1_through46.json)

Results:

- rep2 analysis support: 0 violations over 14,989 rows (511 dim-1, 2,667 dim-4-through-prefix, 11,811 dim-6-through-prefix).
- rep16 analysis support: 0 violations over the same row family.

These witnesses satisfy a stronger earlier CP-SAT model that also included dimensions 2 and 3, all through-fixed dimensions 4--8, and the rank-1 projection.  Hence a correct encoding of the intended analysis row subset for rep2 or rep16 must be satisfiable.

## Status after the correction

Valid proof components retained:

1. Wang's verified `R_F2(T) >= 20` certificate and expanded occupation table.
2. DRAT-verified no-rank-1 A-side branches from earlier analysis.
3. Fixed-E11 second-point reps 17, 20, 84, 160, and 161 from earlier analysis.
4. The exact-k=18 fixed-E11 branch closure from earlier analysis.
5. The rank-1 projection bound that a length-20 admissible support has at most 18 rank-1 directions.

Not valid as proof components:

- `workspace/data/wang_rep2_seqcnt_proof/`
- `workspace/data/wang_rep10_seqcnt_proof/`
- `workspace/data/wang_rep16_seqcnt_proof/`
- the analysis theorem note as originally written.

Open branches restored:

- fixed-E11 representative 2, k=1..17;
- fixed-E11 representative 10, k=1..17 (CP-SAT infeasible evidence remains interesting but lacks a valid proof object);
- fixed-E11 representative 16, k=1..17.

The supported finite-field frontier remains

```text
20 <= R_F2(T_<3,3,3>) <= 23,
```

with no verified `R_F2 >= 21` result yet.

## Next technical direction

Resolution proofs have struggled with these cardinality-dense packing systems when encoded correctly.  The next useful instrument is still a native pseudo-Boolean proof path: encode the rep10 CP-SAT-infeasible row family as OPB and use a VeriPB-checkable solver if one can be installed or built.  If no VeriPB stack is immediately available, first build a small OPB-to-VeriPB workflow on a toy cardinality contradiction, then run the rep10 formulation.  For reps 2 and 16, keep the analysis supports as real counterexamples to too-small row subsets and as guides for adding genuinely new B/C-side information or stronger row families rather than recycling the faulty analysis CNFs.
