# Unconditional Leakage Inequality: Projection Argument

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Mathematical Result

**Theorem (Unconditional Leakage Bound).** For any exact bilinear decomposition
$M_\lambda = \sum_{t \in I_\lambda} b_t c_t^T$ over $\mathbb{F}_2$ and any source $\lambda$,
target $\mu$ (source need NOT be tight):

$$
e_B(\mu) \geq h - d_B - (m_\lambda - r_\lambda)
$$

where $h = |I_\lambda \cap I_\mu|$, $d_B = \dim(U_\lambda \cap U_\mu)$,
$e_B(\mu) = \dim\text{span}(B_\mu) - r_\mu$, and $m_\lambda - r_\lambda$ is the
"slack" of the source.

Equivalently, using $h = (m_\lambda + m_\mu - m_{\lambda \oplus \mu})/2$:

$$
2 e_B(\mu) \geq 2 r_\lambda - m_\lambda + m_\mu - m_{\lambda \oplus \mu} - 2 d_B(\lambda,\mu)
$$

and the analogous C-side inequality.

**Proof (Projection Argument).** Project $\mathbb{F}_2^9$ modulo $U_\mu$. Then:
1. $\pi_\mu(M_\mu) = 0$ since $\text{col}(M_\mu) = U_\mu$.
2. $\text{rank}(\pi_\mu(M_\lambda)) = r_\lambda - d_B$ (kernel of $\pi_\mu|_{U_\lambda}$ is $U_\lambda \cap U_\mu$).
3. Shared terms: each $b_t \in \text{span}(B_\mu) \supseteq U_\mu$, so $\pi_\mu(b_t)$ lies in $\pi_\mu(\text{span}(B_\mu))$, which has dimension $\leq e_B(\mu)$.
4. Non-shared terms: at most $m_\lambda - h$ independent projected vectors.
5. Column space containment: $r_\lambda - d_B \leq e_B(\mu) + (m_\lambda - h)$.

Rearranging: $e_B(\mu) \geq r_\lambda - d_B - m_\lambda + h = h - d_B - (m_\lambda - r_\lambda)$. □

**At source tightness** ($m_\lambda = r_\lambda$): the slack term vanishes, recovering the old bound $e_B(\mu) \geq h - d_B$.

**review verification**: independently confirmed in `independent-verification-record`. The proof works over any field; only the weight form $h = (m_\lambda + m_\mu - m_{\lambda\oplus\mu})/2$ is $\mathbb{F}_2$-specific. review provided a concrete example where ALL sources are non-tight but the bound is tight.

## Pool Verification

Verified on ALL 519 rank-21 E11 pool decompositions:
- **48,248,316** (source, target, side) triples checked
- **Zero violations**
- 2,748,560 non-tight constraints active (5.6× more than 488,052 tight constraints)
- **365,657 binding** non-tight constraints (actual excess equals lower bound)

File: [pool_verification_full.json](../results/unconditional_leakage/pool_verification_full.json)

## L15 and analysis Rejection

The unconditional inequality **rejects both L15 and analysis** near-supports, which were previously immune to the tight-only leakage filter.

### L15: 3 violated targets

| Target $\mu$ | rank | $m_\mu$ | budget | B-source (slack) | C-source (slack) | $e_B$ lb | $e_C$ lb | excess |
|:---:|:---:|:---:|:---:|:---|:---|:---:|:---:|:---:|
| 9 | 1 | 4 | 1 | λ=18 rank-1 (slack 1) | λ=161 rank-2 (slack 1) | 1 | 1 | +1 |
| 18 | 1 | 4 | 1 | λ=5 rank-2 (slack 1) | λ=34 rank-2 (slack 1) | 1 | 1 | +1 |
| 27 | 1 | 4 | 1 | λ=5 rank-2 (slack 1) | λ=35 rank-2 (slack 1) | 1 | 1 | +1 |

### 2 violated targets

| Target $\mu$ | rank | $m_\mu$ | budget | B-source (slack) | C-source (slack) | $e_B$ lb | $e_C$ lb | excess |
|:---:|:---:|:---:|:---:|:---|:---|:---:|:---:|:---:|
| 18 | 1 | 4 | 1 | λ=9 rank-1 (slack 1) | λ=34 rank-2 (slack 1) | 1 | 1 | +1 |
| 27 | 1 | 4 | 1 | λ=6 rank-2 (slack 1) | λ=131 rank-2 (slack 1) | 1 | 1 | +1 |

### Mechanism
All violations follow the same pattern:
- **Target**: rank-1 contraction with $m_\mu = 4 = r_\mu + 1$, giving Sylvester budget = 1
- **B-side source**: slack-1 source (rank-1 or rank-2, $d_B = 0$), giving $e_B \geq 1$
- **C-side source**: different slack-1 source ($d_C = 0$), giving $e_C \geq 1$
- **Combined**: $e_B + e_C \geq 2 > 1 =$ budget → contradiction

The tight-only filter sees **zero** leakage from these slack-1 sources because they are not tight. The unconditional inequality captures the residual leakage from near-tight sources.

File: [l15_violation_details.json](../results/unconditional_leakage/l15_violation_details.json)

## Same-W Comparison

Among 54 shadow+purity survivors in the same-W deletion family:
- **54/54** rejected by tight-only (same as before)
- **54/54** rejected by unconditional (same)
- **53/54** show strictly more violations with unconditional than tight-only

File: [tight_vs_unconditional.json](../results/unconditional_leakage/tight_vs_unconditional.json)

## CP-SAT Formulation

The unconditional inequality eliminates tightness booleans from the CP-SAT model:

| Model | Variables | Tightness bools | Leakage ineqs (B+C) |
|:---|:---:|:---:|:---:|
| Old indicator-guarded | 1132 | 255 | 92,964 (guarded) |
| Old big-M | 877 | 0 | ~82K (weakened) |
| **Unconditional** | **876** | **0** | **92,964 (unconditional)** |

The unconditional model has fewer variables and stronger propagation (all constraints always active).

### CP-SAT Results
| Wang mode | Time | Status | Notes |
|:---|:---:|:---:|:---|
| reduced | 91s | UNKNOWN | same as old models |
| complete | 519s | UNKNOWN | 417,197 rows + 92,964 leakage ineqs |

File: [solve_complete600.json](../results/unconditional_leakage/solve_complete600.json)

## review Implementation Notes

1. `m_expr(0)` returns `s_rank` but $I_0 = \emptyset$, so $m_0 = 0$ by definition. Currently safe since $\lambda \oplus \mu = 0$ only when $\lambda = \mu$, which is skipped. Should be corrected for future extensions.

2. The Boolean `x[p]` model covers only **distinct** 19-direction supports. The inherited repeated-projected-A branch certificate already excludes repeated directions, so this is sufficient for the complete search. For general formulations, multiplicities would require integer $x_p$.

3. Negative-slack entries ($m_\lambda < r_\lambda$) in comparison data come from scalar-violated supports — these are separately excluded and do not serve as evidence for the unconditional inequality's power.

## Key Evidence Files

- [unconditional_leakage.py](../code/unconditional_leakage.py) — main script (verify, solve, compare)
- [violation_diagnostic.py](../../quotient_cores/code/violation_diagnostic.py) — L15/analysis diagnostic
- [pool_verification_full.json](../results/unconditional_leakage/pool_verification_full.json) — 519-row verification
- [tight_vs_unconditional.json](../results/unconditional_leakage/tight_vs_unconditional.json) — tight vs unconditional
- [l15_violation_details.json](../results/unconditional_leakage/l15_violation_details.json) — violation details
- [solve_complete600.json](../results/unconditional_leakage/solve_complete600.json) — complete Wang solve
- `independent-verification-record` — review verification

## DFS Pilot Results

### Infrastructure
Built [wang_leakage_dfs.py](../code/wang_leakage_dfs.py): orderly DFS with Wang + unconditional leakage pruning.

### Branch-1 Pilots

| Wang rows | Cap limit | Time | Nodes | Wang prunes | Leak prunes | Solutions | Timeout |
|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| 35,351 | ≤2 | 60s | 420,795 | 3,542,461 | 0 | 331,858 | yes |
| 417,197 | all | 90s | 7,084 | 290,722 | 0 | 0 | yes |

### Observations
1. With all Wang rows, the DFS is very slow (~78 nodes/sec) due to per-node overhead of checking affected rows among 417K total.
2. With cap-≤2 only, throughput is ~7,000 nodes/sec but too many solutions survive.
3. Leakage pruning doesn't fire on partial supports because the conservative check allows maximum future budget growth (rank-1 targets have max_future_budget = 16, while partial leakage bounds rarely exceed this).

### Next Steps for DFS Approach
1. **Tighter partial-support leakage check**: For a partial support of size k with remaining = 19-k, bound future m_λ increments using the available point set and Wang constraints. If the remaining points are few enough that m_μ can't increase enough to accommodate the leakage, prune.
2. **Bitwise acceleration**: Use bitmask representation for Wang row membership to speed up per-node checks.
3. **Hierarchical constraint ordering**: Start with cap-≤2 and add cap-3, cap-4, ... lazily as the partial support grows.
4. **SAT alternative**: Encode the support + unconditional leakage as a SAT/pseudo-Boolean problem for CaDiCaL with DRAT output.
