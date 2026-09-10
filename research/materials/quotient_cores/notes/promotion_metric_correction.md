# correction: promotion selectors and model-violation counts

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

The analysis handoff used a misleading operational rule: keep selective complete-row promotion only when the next SAT model has fewer complete-LUT violations.  That rule is not mathematically justified for the lower-bound program.

CaDiCaL is asked to find any satisfying assignment of the currently encoded formula, not to minimize the number of unencoded Wang-row violations.  Adding a valid Wang occupation consequence strictly shrinks the encoded support set, but the next satisfying assignment can have many more violations of rows that remain unencoded.  This does not mean the added inequality was weaker or harmful for an eventual UNSAT proof.  Conversely, a lower violation count for the next returned model need not mean the formula is closer to excluding all supports.

The correct separation is:

- **Candidate quality / construction heuristic:** if searching for an admissible support or a tensor decomposition, the full-LUT violation count of a returned support can be a useful heuristic signal.
- **Exclusion strength / lower-bound proof:** the useful measure is whether added valid consequences eliminate families of supports, improve bounded decision/proof outcomes, produce smaller or replayable UNSAT certificates, or create a structurally interpretable contradiction.  Single returned-model violation counts are only descriptive diagnostics.

Therefore the analysis pilots should be reinterpreted as follows:

- Historical-row promotion, low-residual current-model promotion, and high-excess current-model promotion produced different valid encodings with different sizes and different solver-returned candidates.
- They did **not** establish that high-excess promotion harms the lower-bound route, nor that low-residual promotion is inherently better.  Evidence about solver cost, proof closure, proof size, or eliminated support families would be needed for such a conclusion.
- Complete promoted Wang rows remain a useful capability, especially as a way to convert repeatedly or strategically implicated rows from model-specific witness clauses into globally enforced consequences.  Selector choice should be tested by bounded SAT/UNSAT/proof comparisons and by structural coverage, not by monotone decreases in violation count.
- The k=5 idx13 result is the key lesson: the stored formula already contained a contradiction while its status was `SOLVER_UNKNOWN`; a longer fair solve with proof replay closed the branch without adding promotion.  Existing seed CNFs should be solved fairly and replayed before launching additional separation.

Practical continuation:

1. Use fair seed solves on stored `SOLVER_UNKNOWN` or `MAX_ROUNDS` formulas before adding constraints.
2. If a seed is SAT, promotion selectors may be compared, but all promoted rows are valid Wang consequences regardless of the next model's violation count.
3. Count a branch as closed only after exact CNF regeneration, row provenance checks, auxiliary-interval checks when counters are used, and independent proof replay.
4. Keep rep2 separate from matching strata.  Its 17-orbit stabilizer structure suggests symmetry-aware or orbit-aware branching/proof construction may matter more than a larger pool of model-specific clauses.
