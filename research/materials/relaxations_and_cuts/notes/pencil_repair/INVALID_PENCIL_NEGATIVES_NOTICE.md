# correction of analysis pencil negatives

> Historical research record. Read with the [correction guide](../../../../corrections.md); recorded conclusions are not new verification receipts.

Do not use the analysis reported `pencil_infeasible` entries as necessary support cuts.

The file [analytical_pencil_results.json](../../results/pencil_pilot/analytical_pencil_results.json) classified the flagship lines `[42,149,191]` and `[55,141,186]` by random search, not by exhaustive algebra.  The random search also sampled rank-`c11` factorizations, whereas the pencil condition allows `rank(Z) <= c11`.  Lower-rank witnesses exist.

Repaired evidence:

- [pencil_constructive_repair.json](../../results/pencil_repair/pencil_constructive_repair.json) constructs explicit witnesses for the flagship cases and checks the original 9x9 rank inequalities:
  - `[42,149,191]`, budget `(c10,c01,c11)=(3,6,7)`: ranks `(rank(M1+Z),rank(M2+Z),rank(Z))=(3,6,6)`.
  - `[55,141,186]`, budget `(3,6,7)`: ranks `(3,6,6)`.
- The same file reclassifies all 100 stored analysis test records: 34 old feasible records remain feasible and 66 old negative records are constructively feasible by the block envelope.
- For the analysis near-miss support, the block-diagonal envelope realizes all 192 all-rank-9 dual-line budgets previously considered.
- [pencil_boundary_fast.json](../../results/pencil_repair/pencil_boundary_fast.json) compares the block-diagonal envelope with individual contraction bounds for all 10,795 dual lines and all length-19 color budgets.  The block envelope is not universally identical to individual bounds; 5,567 lines have budgets allowed by individual bounds but not covered by this structured construction.  This only means the structured construction is incomplete, not that the budgets are impossible.
- [pencil_factor_cpsat_line_42_149_191_minimal.json](../../results/pencil_repair/pencil_factor_cpsat_line_42_149_191_minimal.json), `pencil_factor_cpsat_line_42_95_117_minimal.json`, and `pencil_factor_cpsat_line_42_87_125.json` give exact SAT-model witnesses for the all-rank-9 minimal budgets `(4,5,5)`, `(5,4,5)`, and `(5,5,4)` in several representative lines, including the flagship line.  These witnesses further weaken the idea that all-rank-9 pencil color budgets separate supports beyond individual contractions.

Current safe interpretation: the dual-line pencil is a correct local realizability formulation, but analysis did not establish any negative support consequence.  Future use must be based on explicit witnesses, exact full pencil boundary analysis, or replayable proof objects; random non-discovery is not evidence of impossibility.

Follow-up after review and audit:

- [allrank9_subspace_boundary.json](../../results/pencil_repair/allrank9_subspace_boundary.json) stores 192/192 all-rank-9 line records with explicit `K,AK,e` data and three witnesses for the central triples `(4,5,5)`, `(5,4,5)`, `(5,5,4)`.  `failure_count=0`.
- [pencil_repair_audit.json](../../results/pencil_repair/pencil_repair_audit.json) independently recomputes the saved witnesses and analysis colors; `failure_count=0`, `warning_count=0`.
- review check `independent-verification-record` agreed with the invalidation and all-rank-9 interpretation, while noting the corrected kernel statement `AK ⊂ ker(I+W)` and `K ⊂ ker(A+W)`.
