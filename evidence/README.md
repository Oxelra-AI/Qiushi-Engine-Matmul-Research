# Evidence Map

| Claim or boundary | Evidence |
| --- | --- |
| Tensor convention and structural contradiction | [Main report](../reports/en/main.pdf) and [elementary-matrix check](../proof/assets/structural/scripts/product_formula_full_elementary_matrix_check.py) |
| Earlier quotient lower bounds | [Pinned Wang certificate](../proof/assets/quotients/data/wang_f2_lb20/cert_matrix_q02_n333.pb.txt) and independently expanded lookup table |
| Eight strengthened two-plane bounds | [CNF/DRAT certificates](../proof/assets/occupation/data/dim2_cnf_cert_all) and [primary encoder](../proof/assets/occupation/scripts/dim2_cnf_cert.py) |
| Encoding is about integer counts | [Semantic reconstruction](../proof/assets/occupation/scripts/dim2_independent_semantics.py), positive controls and [separate unary implementation](../proof/assets/structural/scripts/transparent_unary_dim2_cnf.py) |
| Fresh mathematical replay | [Recorded primary replay](verification.json); running verification creates a new result rather than accepting an old success |
| Closed Lean theorem and finite premises | [Formalization coverage](../formalization/COVERAGE.md) and [six-group kernel verification](../formalization/verification-results.json) |
| Maintained document identity | [Original reports](report-build.json) and [Lean-integrated reports](lean-report-build.json) |
| Shared figure sources | [Image and source identities](figures.json) |
| Public snapshot identity | [Release manifest](release-manifest.json) |
| Research development and corrections | Appendix B of the report and [thematic research map](../research/README.md) |
| Included notes, plans, programs and experiment records | [Artifact catalog](../research/catalog.json) and [coverage receipt](research-coverage.json) |
| Redacted historical labels and cache metadata | [Check labels](proof-metadata-redaction.json) and [binary cache labels](cache-metadata-redaction.json); mathematical data are preserved |

Appendix C of the [report](../reports/en/main.pdf) briefly compares the
structural argument with contemporaneous work.

No private transcript or execution-control database is included.
`make privacy` inspects the current public files; it does not rely on an old
scan receipt. The release packaging command includes this check.
Hash identity proves that specified bytes agree; it does not prove
mathematical novelty, external review, or publication acceptance.
