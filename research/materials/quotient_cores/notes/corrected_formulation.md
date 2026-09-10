# Corrected E11 Core Formulation — research research_record analysis

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## ERRATUM

The original `e11_formulation_and_lift.md` contained an error in the B-block analysis:
> "If q_s ≠ 0: all lifted terms with nonzero B-block-s component share the SAME direction q_s"

This is **FALSE**. A rank-1 SUM does not imply each summand shares the same left factor.
Counterexample: (e₁+e₂)⊗r + e₂⊗r = e₁⊗r. Independently caught by review, research_record, and review.

The correct statement: the SUM's column space is contained in ⟨q_s⟩ (rank ≤ 1), but individual terms can have arbitrary directions that cancel.

## Master Dichotomy (from review + independent derivation)

Let ρ = R_{F₂}(E11 core). Two verified facts give a clean dichotomy:

1. **Bridge** (verified in this investigation): rank-r core CPD → rank-(r+3) full T CPD
2. **Reduction** (DRAT-proved): rank-20 full T → has rank-1 A-factor → normalize to E₀₀ → project: core gets ≤ 19-term representation → ρ ≤ 19

Therefore:
$$\rho \leq 19 \Longrightarrow R(T) \leq 22$$
$$\rho \geq 20 \Longrightarrow R(T) \geq 21$$

**Within the E11 route, deciding whether the core has rank 19 is enough to achieve one of the two requested breakthroughs.**
- Find rank-19 core → immediate rank-22 full algorithm (no lift condition needed).
- Prove ρ ≥ 20 (core UNSAT at rank 19) → immediate R(T) ≥ 21, after the full rank-20 no-rank-one reduction has been independently replayed.

These are implications for the E11 surface, not biconditionals for the global tensor rank. A full rank-22 algorithm could exist outside this E11 core route, and a global lower bound stronger than 20 could in principle be proved by a different mechanism. The lift condition is needed only for the narrower question "can a particular rank-19 core sit inside a full rank-20 decomposition?" — i.e. if ρ = 19 and the exact-rank-20 question becomes central.

## Corrected Lift Framework (contingency, not primary)

The lift condition remains mathematically valid as a framework for excluding rank-20 full decompositions:
- rank(M₀ + Δ) ≤ 1 where Δ = sum_{ε=1} v_t ⊗ w_t
- B-block SUM equations (correct): sum_{lifted} v_t^{(s)} ⊗ w_t = q_s ⊗ r (rank ≤ 1)
- ε ∉ colspan(U) is a strict necessary condition (review key insight)
- The general block coupling: Φ_{ji}(ε) = δ_{j0}δ_{i0} I₃ + q_j ⊗ r_i

## Calibration Evidence

Exhaustive test on 3 rank-21 E11 core decompositions, all 2²¹ lift assignments each:
- Decomp 0: 0/2,097,152 rank-≤1 (min rank observed: 3, at 0.005%)
- Decomp 1: 0/2,097,152 rank-≤1 (min rank observed: 3, at 0.005%)
- Decomp 2: 0/2,097,152 rank-≤1 (min rank observed: 3, at 0.011%)
- Total: **0/6,291,456** assignments gave rank ≤ 1

The lift condition is extraordinarily tight even for rank-21 decompositions (which have MORE terms to choose from than rank-19).

## Corrected Research Priority

### Primary: Determine E11 core rank ρ

**Route A (upper bound)**: Find a rank-19 E11 core CPD.
- 19 terms × (8+9+9) = 494 binary unknowns
- 648 Brent equations mod 2
- SAT encoding with ~500 base variables
- Block-diagonal structure provides strong propagation
- Any solution immediately verified by the lift script → rank-22 full T

**Route B (lower bound)**: Prove ρ ≥ 20 (no rank-19 core exists).
- Same encoding, prove UNSAT
- Would immediately give R(T) ≥ 21 without needing lift analysis
- Requires DRAT/LRAT certificate + semantic correctness verification

### Secondary: Lift obstruction (only if ρ = 19)

If a rank-19 core is found, the lift question becomes a SMALL finite computation:
- Fix the core (u, v, w all known constants)
- Only unknowns: ε ∈ F₂¹⁹, q ∈ F₂⁹, r ∈ F₂⁹ (37 bits total)
- Linear map L: F₂¹⁹ → F₂⁸¹ defined by L(ε) = sum ε_t v_t w_t^T
- Check if M₀ + im(L) intersects rank-≤1 variety
- Exhaustive: only 2¹⁸ possible (q,r) pairs × preimage computation

## SAT Encoding Plan for Core-Only Problem

Variables (per term t = 1,...,19):
- u_t[s] for s = 0,...,7 (A-factor, 8 bits)
- v_t[b] for b = 0,...,8 (B-factor, 9 bits)
- w_t[c] for c = 0,...,8 (C-factor, 9 bits)
Total: 19 × 26 = 494 base + Tseytin auxiliary

Equations: For each (s, b, c):
sum_{t: u_t[s]=1} v_t[b] · w_t[c] = core[s,b,c]  (mod 2)
= 648 trilinear equations, each Tseytin-linearized

Symmetry breaking:
- Fix u_1 (lexicographic first)
- Order remaining terms by u_t
- Each slice needs ≥ 3 participating terms
- Total A-weight ≥ 24

Structural cuts:
- Block XOR/trace consequences (redundant but propagation-helping)
- Wang occupation constraints (from verified certificate)

## Files

- Bridge verification: [bridge_verification.json](../results/e11_bridge/bridge_verification.json)
- Lift obstruction: [lift_obstruction_analysis.json](../results/lift_obstruction/lift_obstruction_analysis.json)
- Calibration: [lift_calibration_rank21.json](../results/lift_calibration/lift_calibration_rank21.json)
- Original (contains error): [e11_formulation_and_lift.md](e11_formulation_and_lift.md)
- This corrected note: [corrected_formulation.md](corrected_formulation.md)
