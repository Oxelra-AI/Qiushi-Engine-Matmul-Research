# Unconditional Quotient-Rank Inequalities for E11 Core

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Mathematical Result

**Theorem (Unconditional Quotient-Rank Bound).** Let $T = \sum_{t=1}^s a_t \otimes b_t \otimes c_t$ be an exact tensor decomposition over $\mathbb{F}_2$. For any set of *source* contractions $S = \{q_1, \ldots, q_k\}$ with contraction ranks $r_{q_i} = \operatorname{rank} L(q_i)$ and weights $w_{q_i} = |\{t : q_i(a_t) = 1\}|$, define

$$W = \sum_{q \in S} \operatorname{col} L(q)$$

and for any *target* contraction $t$, define $R = \operatorname{rank}(\pi_W L(t))$ and $N_{\text{out}} = |\{j : t(a_j)=1 \text{ and } q(a_j)=0 \text{ for all } q \in S\}|$. Then:

$$N_{\text{out}} + \sum_{q \in S} (w_q - r_q) \geq R.$$

No source or target needs to be saturated. The C-side statement is identical.

**Proof.** The B-factors $\{b_j : q(a_j)=1\}$ span a space $V_q$ of dimension $\leq w_q$ containing $\operatorname{col} L(q)$ (dimension $r_q$). Since $\operatorname{col} L(q) \subseteq W$, we have $\dim(V_q \bmod W) \leq w_q - r_q$. The target's projected rank satisfies $R \leq \dim(\text{outside B-span mod } W) + \sum_q \dim(V_q \bmod W) \leq N_{\text{out}} + \sum_q (w_q - r_q)$. $\square$

**As a linear constraint in multiplicity variables $x_p$:**

$$\sum_{\substack{p:\, t(p)=1 \\ q(p)=0\;\forall q \in S}} x_p + \sum_{q \in S} \left(\sum_{p:\,q(p)=1} x_p - r_q\right) \geq R$$

This is purely linear in $x_p$; no saturation-guard Boolean variables are needed.

## Comparison with Guarded Version

The analysis guarded version required $\operatorname{sat}(q_1) \wedge \operatorname{sat}(q_2) \Rightarrow N_{\text{out}} \geq R$, which needs auxiliary Boolean variables and big-M encoding. When sources are saturated ($w_q = r_q$), the unconditional version reduces to $N_{\text{out}} \geq R$, recovering the guarded cut. When a source becomes nonsaturated by 1 ($w_q = r_q + 1$), the guarded cut is inactive but the unconditional version still requires $N_{\text{out}} \geq R - 1$.

## Validated Results

1. **cn122 E11 core control**: 21 terms, sources 150,176 (rank 6 each) with target 107 (B-side).
   - Sources are NOT saturated (excess = 10), so guarded cut is inactive.
   - Unconditional LHS = 13 ≥ 3 = R. Passes with slack 10. ✓

2. **analysis round-5 bad support**: Sources ARE saturated (excess = 0).
   - Both guarded and unconditional detect the violation (LHS=2 < R=3). ✓

3. **All pair-source unconditional violations on cn122**: ZERO violations. ✓

4. **Unconditional MILP with repeat-forced constraint**: HiGHS returns **INFEASIBLE** in 23.8s using 12,165 Wang rows + 252 unconditional cuts (pure ILP, 261 variables, 12,686 constraints). This independently confirms the repeated-direction E11 core exclusion without saturation Booleans.

5. **Guarded MILP replay (comparison)**: HiGHS also INFEASIBLE in 29.0s but needs 290 variables and 12,744 constraints (extra saturation variables/big-M).

6. **Without repeat constraint**: Model 2 is FEASIBLE — distinct supports survive the stored learned cuts. The feasible solution has 95 complete Wang violations, showing distinct-point coverage is incomplete.

7. **LP relaxation**: FEASIBLE in both with-repeat and without-repeat cases, confirming the integrality gap is essential.

## Fresh Unconditional Separator (Pilot)

A 10-round pilot using unconditional cuts (no repeat constraint, covering both distinct and multiset) learned:
- 516 unconditional quotient-rank cuts
- 12,472 active Wang rows
- Final status: OPTIMAL (not yet infeasible)

Round 8 produced the strongest E11 core candidate to date:
- 19 distinct A-points: [2,3,4,10,20,22,32,36,73,86,96,97,108,162,180,224,233,245,252]
- 15 complete Wang violations (previous best: 16 from analysis v3 round12)
- Zero zero-domain terms, linear membership passes (affine dim 747), zero transversal failures, zero quotient-rank violations

The 15 violated subspaces are in dimensions 4-6 with L=12,15.

## Complete Core Table Test

Built the MILP/CP-SAT with ALL 417,198 Wang rows + 255 contraction bounds:
- **LP relaxation**: FEASIBLE in 11.7s. Solution: 96 nonzero, all fractional, max=0.776.
  No dual-ray certificate is available; the integrality gap is real.
- **HiGHS ILP**: TIME LIMIT at 300s (neither feasible nor infeasible found).
- **CP-SAT with 516 qcuts**: UNKNOWN at 600s.

The E11 rank-19 core question over F₂ is a genuine open integer feasibility problem.

## Background 50-round Separator

The 50-round run reached UNKNOWN at round 10 (300s solve). Wang violations
decreased from 161 to 85 over 10 rounds; 388 unconditional cuts were learned.
Round 9 was the best: 85 Wang violations, 0 zero-domain, 0 transversal, 0 qcut
violations, linear pass (affine dim 666), but distinct=18 with max_mult=2.

## Violation Structure of Best Candidates

The pilot round-8 candidate (15 Wang violations, 19 distinct points) had ALL
violations with excess exactly 1. Point p=162 appeared in 10/15 violations.
The 15 violated subspaces were in dimensions 4-6 with L=12,15.

## Open Work

1. The complete 417K-row ILP needs longer runs (SAT/PB encoding or longer MILP/CP-SAT).
2. The pilot round-8 candidate (15 Wang violations) is the best distinct E11 target.
3. The repeated-direction exclusion is confirmed by three solvers but lacks a formal proof certificate.
4. The joint B+C inequality (Sylvester strengthening) doesn't help for current best candidates.
5. The unconditional inequality generalizes to k sources and may yield stronger cuts from triples.
