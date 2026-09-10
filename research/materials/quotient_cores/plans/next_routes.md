# next research routes for research_record

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

this investigation remains in Explore. Do not start final writing. The goal is still an exact rank <=22 construction or a rigorous rank-23/lower-bound result over a stated field/structure.

Primary preserved note: [frontier_.md](../../exact_baselines/notes/frontier_.md).
Verified rank-23 baseline: [scheme-47fa58e6cd.qmm](../../exact_baselines/results/cn122_3x3_r23_repro/scheme-47fa58e6cd.qmm) with receipt `receipt.json`; runtime says integer rank 23, Python/native agree on all 729 Brent equations.

## Best next work

1. Locate and verify Wang 2026 F2 lower-bound certificate.
   - Source paper read path: `Knowledge/objects/papers/Automated-Lower-Bounds-for-Small-Matrix-Multiplication-Complexity-over-F--d7e0d98ca98f--3c257f9fb1dd/object.md`.
   - Runtime interface: `qiushi-matmul lower-bound verify-wang-q2-333 <certificate>`.
   - Need to find certificate path inside the pinned source `tensor-rank-lower-bound` (use `qiushi-matmul source path tensor-rank-lower-bound` then inspect via shell/listing). Verify locally, save receipt/output under `workspace/data/wang_f2_lb20/`, and read verifier/source enough to understand proof object structure.
   - Scientific purpose: establish a checked finite-field lower-bound baseline and identify what blocks extension from 20 toward 21/22/23.

2. Inspect the rank-22 SAT benchmark semantically, not by launching a blind long search.
   - Knowledge repo note: `Knowledge/objects/code/matrix-challenges--687bcef3570e--8594c00d57bd/object.md`.
   - Runtime source: `matrix-challenges` @ `150b2e2...`.
   - Examine `challenge4/` size, CNF variables/clauses, and encoder source under `src/` to map DIMACS variables back to Brent base variables. Save a short semantic map in `workspace/notes/`.
   - Scientific purpose: know what exactly Challenge 4 asks over F2 and what constraints/normal forms it includes or omits.

3. Deepen the symmetry/equivalence frontier from de Groote, Ballard, Heule, and Yang.
   - Already read: Ballard 2018, Heule 2019, Yang 2024, Kauers--Moosbauer 2022 excerpts.
   - Need full targeted reading of sections on de Groote action, type-3 core, canonical forms, and rank-redundancy constraints. This supports both lower-bound certificate interpretation and semantic search design.

4. Treat metadata-only rank-23 proof or rank-22 obstruction claims with skepticism.
   - Retrieval found metadata-only Zenodo-like claims (`arron2026tensor`, `beuchert2026contact`) but no full proof package read or verified. They should not be cited as established. If pursued, retrieve/read full artifact and independently check the core invariant before it affects route choice.
