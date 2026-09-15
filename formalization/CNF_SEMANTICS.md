# Boolean-Copy and CNF Semantics

This private, standalone addition covers the encoding mathematics in
`reports/en/main.tex`, under "Eight Two-Dimensional DRAT Proofs" (especially
the Boolean-copy/equisatisfiability paragraphs around lines 407-409). It does
not replace, rebuild, or modify the parent's already-closed main certificate.
All six implementation modules are independent of that certificate closure.

## Verified Coverage

| Report claim | Kernel-checked result in namespace `Qiushi.CNF` |
| --- | --- |
| Bounded nonnegative integers can be represented by unrestricted Boolean copies | `bounded_integer_iff_copies`, `bounded_iff_copies` |
| Exactly the intended count is recovered; any count-dependent constraints transfer | `copyCount_threshold`, `bounded_system_iff_copies` |
| Each 0/1 occupation row counts precisely its expanded copies | `row_sum_copies`, `copy_row_int`, `copy_occupation` |
| Singleton caps and clipping to the target do not lose legal counts | `singleton_caps_entailed` and `singleton_occupation_cnf_equisatisfiable` |
| Satisfied cardinality constraints extend to sequential counters, and conversely | `atMostCNF_correct`, `rowCNF_correct`, `atLeastCNF_correct` |
| Matching upper/lower bounds encode exact total weight | `exact_two_counters`, `booleanSystemCNF_correct` |
| Separate counters' auxiliary assignments coexist | `disjoint_extensions_iff`; dependent sum tags make auxiliary blocks disjoint |
| Removing duplicate clauses or tautologies cannot destroy the witness | `clauses_subset_preserves_sat`, `sat_dedupCNF`, `eval_dedup_literals`, `tautological_clause`, `omit_satisfied_cnf` |
| The complete bounded occupation system is equisatisfiable with a concrete CNF | `occupation_cnf_equisatisfiable` |
| Transparent unary witnesses are monotone and recover their counts | `threshold_monotone`, `copyCount_threshold` |
| Transparent reverse prefix clauses and terminal units encode an exact total | `exactPrefixCNF_correct`, with explicit hypothesis `0 < n` |

Caps may be zero; row right-hand sides may be negative; the target and sets may
be empty. `rowCNF_correct` includes contradiction, zero-unit and tautological
branches. No existence, satisfiability, or correctness of any particular orbit
is assumed by the generic theorems. The singleton-cap theorem has the explicit
`SingletonCapSource` hypothesis: each selected cap is the initial target or
the bound of an actual singleton row. This is sufficient; optimality of that
selection is not required for soundness.

`occupationCNF` is an actual `Std.Sat.CNF`, with finite sets enumerated through
Mathlib's verified `Finset.equivFin`. Its primary variables are the dependent
sum `(q : Q) x Fin (cap q)`. Each row and the two total bounds have separately
tagged auxiliary pairs. A fixed-false dummy primary variable handles empty
enumerations. The standalone concrete formula is not a serialization of the
release's DIMACS files.

## Encoding Boundary

The primary Python source `dim2_cnf_cert.py` calls
`CardEnc.atmost(..., vpool=pool, encoding=EncType.seqcounter)`. Its installed
Python wrapper delegates to `pycard.encode_atmost` and updates the shared pool.
The C++ implementation and concrete ID allocation are **not** verified here.
The copy representation, signed/complement cardinalities, singleton clipping,
and disjoint-extension mathematics are covered independently of that call.

The explicit clauses formalized here are the transparent encoder's
`add_row_atmost_forward` and `add_total_exact_prefix`: input-to-first-threshold,
prefix carry, prefix increment, both reverse implications, and terminal units.
The row wrappers preserve the Python negative/zero/tautological cases. Lean
groups reverse clauses separately, so the comparison is clause-multiset
equality after literal normalization, not byte or ordering identity.

Small-instance checks compare 45 Lean-exported formulas directly with the
unmodified public transparent encoder, checking 351 primary assignments and
133 exhaustive auxiliary-extension cases. This is regression evidence, not
the basis of the universal proofs. The test's `#eval` only exports examples;
no theorem depends on it or on Python output.

The transparent exact-counter function reserves but does not constrain its
zero-prefix row. For `n = 0, target = 1`, its two terminal units are satisfiable
although the empty input has weight zero. The test explicitly reproduces this
edge case; `exactPrefixCNF_correct` therefore requires `0 < n`. The report's
positive-length, target-18 use is not that edge case. The upper/lower-counter
encoding used in `occupationCNF` has no such precondition.

Not covered: orbit cap histograms or row counts, Wang-table reconstruction,
PySAT implementation refinement, numeric pool allocation, binding these generic
formulas to any frozen CNF hashes, DRAT checking/replay, or a new connection
from the existing tensor theorem to the released CNF bytes. No such claim is
made by the evidence.

## Exact Types and Axioms

`tests/CNFSemanticsAxioms.lean` checks the fully applied types and prints the
transitive axioms of all 67 theorems, including helpers. The complete compiler
output is in `evidence/cnf-semantics/statements-and-axioms.log`.

The dependency union is only `propext`, `Classical.choice`, and `Quot.sound`.
There are no custom axioms, `sorry`, `admit`, or `native_decide`. Ordinary
`decide`, simplification, arithmetic tactics, and finite-sum lemmas produce
kernel-checked proof terms. `Std.Sat.CNF` provides clause/formula evaluation,
conjunction and relabeling; this addition does not invent a SAT trust oracle.

## Reproduction

Use the parent's pinned Lean 4.33.1 / Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474` environment receipt. Set `ENV_JSON`
to the supplied `build-20260914-125249/environment.json`; dependencies and
parent outputs are read-only imports. From this private worktree root:

```bash
python3 formalization/tools/build_cnf_semantics.py --environment "$ENV_JSON" \
  --output formalization/.local/cnf-semantics-clean \
  QiushiBooleanCopies QiushiSequentialCounter QiushiCNFDisjoint \
  QiushiCardinalityCNF QiushiExactPrefixCNF QiushiOccupationCNF \
  tests/CNFEncodingSamples tests/CNFSemanticsAxioms
python3 formalization/tools/verify_cnf_semantics.py \
  --build-dir formalization/.local/cnf-semantics-clean
```

The targeted builder invokes Lean directly, with warnings treated as errors;
it never runs Lake, fetches dependencies, or rebuilds the parent. Compiler
receipts and `.olean` files remain under the private build directory. The
verifier checks source/object digests, successful exits, complete axiom-log
coverage and the small Python cross-check before writing the evidence receipt.
Development used at most two simultaneous compiler processes; the reproduction
command uses one.
