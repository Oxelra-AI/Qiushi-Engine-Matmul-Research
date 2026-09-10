# E11 Core Formulation and Lift Obstruction — research research_record

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Notation and Convention

- $T = T_{\langle 3,3,3 \rangle} \in \mathbb{F}_2^{9 \times 9 \times 9}$, defined by $T[3i+j, 3j'+k, 3i'+k'] = \delta_{i,i'}\delta_{j,j'}$
- A-coordinates: $a_{ij}$ at index $3i+j$ for $i,j \in \{0,1,2\}$
- B-coordinates: $b_{jk}$ at index $3j+k$
- C-coordinates: $c_{ik}$ at index $3i+k$
- Block structure: 9×9 B⊗C matrix has 3×3 blocks. Block $(s,t)$ occupies rows $3s{:}3s{+}2$, cols $3t{:}3t{+}2$.
- Slice $a_{ij}$ of $T$ is $I_3$ in block $(j,i)$ and zero elsewhere.

## E11 Core

**Definition**: E11 core = $T[1:9,:,:] \in \mathbb{F}_2^{8 \times 9 \times 9}$.
- Mask = 1, pivot = 0 ($a_{00}$), no free bits.
- Each core slice $s = 0,\ldots,7$ (A-index $s+1$) is $I_3$ in its assigned block.
- nnz = 24 (3 per slice).

**Block assignments** (verified in [bridge_verification.json](../results/e11_bridge/bridge_verification.json)):

| Slice | A-index | Label | Assigned block $(j,i)$ | B-block | C-block |
|-------|---------|-------|------------------------|---------|---------|
| 0     | 1       | $a_{01}$ | (1,0) | 1 | 0 |
| 1     | 2       | $a_{02}$ | (2,0) | 2 | 0 |
| 2     | 3       | $a_{10}$ | (0,1) | 0 | 1 |
| 3     | 4       | $a_{11}$ | (1,1) | 1 | 1 |
| 4     | 5       | $a_{12}$ | (2,1) | 2 | 1 |
| 5     | 6       | $a_{20}$ | (0,2) | 0 | 2 |
| 6     | 7       | $a_{21}$ | (1,2) | 1 | 2 |
| 7     | 8       | $a_{22}$ | (2,2) | 2 | 2 |

**Removed slice** $T[0,:,:]$: $I_3$ in block $(0,0)$, rank 3 = three elementary terms $(1,1,1), (1,2,2), (1,4,4)$.

## Bridge Theorem (verified)

**Theorem (E11 lift)**: A rank-$r$ CPD of the E11 core lifts to a rank-$(r+3)$ CPD of $T$.
- Lift: shift A-masks left 1 bit (embed in bits 1..8), add removed slice terms.
- Target: rank-19 core → rank-22 full (the research target).
- Positive control: rank-21 core → rank-24 full (verified, diff=0).

**File**: [bridge_verification.json](../results/e11_bridge/bridge_verification.json)

## Rank-20 Reduction Theorem

**Theorem (research_record analysis, DRAT-verified)**:
Any rank-20 decomposition of $T$ over $\mathbb{F}_2$ must contain at least one rank-1 A-factor (as a 3×3 matrix).

*Proof*: Rank-3 branch CNF and rank-2 branch CNF are both DRAT-verified UNSAT under dim≤3 Wang constraints. So all 20 A-factors cannot all have matrix rank ≥ 2. QED.

By GL(3) × GL(3) symmetry on A-space, all rank-1 matrices are equivalent, so we can normalize the rank-1 A-factor to $E_{00}$.

## The Complete Rank-20 Interface

**Setting**: Suppose $T = \sum_{t=0}^{19} a_t \otimes b_t \otimes c_t$ is a rank-20 decomposition. By the reduction theorem, normalize $a_0 = E_{00}$ (mask = 1).

**Core decomposition**: The remaining 19 terms $\{(a_t, b_t, c_t)\}_{t=1}^{19}$ form an E11 core CPD. Define:
- $u_t \in \mathbb{F}_2^8 \setminus \{0\}$: the 8-bit core A-factor (bits 1..8 of $a_t$)
- $\varepsilon_t := a_t[0] \in \{0,1\}$: the lift bit
- $v_t, w_t \in \mathbb{F}_2^9$: B and C factors

**Core equations**: For each slice $s = 0,\ldots,7$:
$$\sum_{t: u_t[s]=1} v_t \otimes w_t = \text{core}[s]$$
This is an 8 × 9 × 9 tensor equation: 648 scalar equations mod 2.

**Slice-0 equation** (the removed $a_{00}$ slice):
$$b_0 \otimes c_0 + \sum_{t: \varepsilon_t=1} v_t \otimes w_t = M_0$$
where $M_0 = I_3$ in block $(0,0)$, zero elsewhere.

**Lift condition**: Rearranging:
$$b_0 \otimes c_0 = M_0 + \Delta, \quad \Delta := \sum_{t: \varepsilon_t=1} v_t \otimes w_t$$
Since $b_0 \otimes c_0$ has rank ≤ 1:
$$\boxed{\mathrm{rank}_{\mathbb{F}_2}(M_0 + \Delta) \leq 1}$$

## Structure of the Lift Condition

Write $M_0 + \Delta = q \otimes r$ for some $q, r \in \mathbb{F}_2^9$. Then $\Delta = M_0 + q \otimes r$.

**Rank distribution of $\Delta$** (exhaustive computation, `workspace/data/lift_obstruction/`):

| rank($\Delta$) | Count of $(q,r)$ pairs |
|---|---|
| 0 | 0 |
| 1 | 0 |
| 2 | 28 |
| 3 | 8100 |
| 4 | 254016 |

Key: $\Delta$ always has rank ≥ 2. The lifted subset must contribute at least 2 nontrivially.

### Block decomposition of the lift condition

Write $v_t = (\alpha_t, \beta_t, \gamma_t)$ and $w_t = (a_t, b_t, c_t)$ with each component in $\mathbb{F}_2^3$ (B-blocks and C-blocks respectively). Then block $(s,t)$ of $v \otimes w$ is $\{α,β,γ\}_s \otimes \{a,b,c\}_t$.

For $q = (q_0, q_1, q_2)$ and $r = (r_0, r_1, r_2)$ (3-component decomposition):

**B-block 0**: $\sum_{\varepsilon_t=1} \alpha_t \otimes w_t = [I_3 + q_0 \otimes r_0 \mid q_0 \otimes r_1 \mid q_0 \otimes r_2]$
**B-block 1**: $\sum_{\varepsilon_t=1} \beta_t \otimes w_t = q_1 \otimes r$ (rank ≤ 1)
**B-block 2**: $\sum_{\varepsilon_t=1} \gamma_t \otimes w_t = q_2 \otimes r$ (rank ≤ 1)

### Critical constraint: B-block rank-1 factorization

For B-block $s \in \{1,2\}$: $\sum_{\varepsilon_t=1} v_t^{(s)} \otimes w_t = q_s \otimes r$.

**If $q_s \neq 0$**: Every lifted term with $v_t^{(s)} \neq 0$ must have $v_t^{(s)} = q_s$ (single direction in B-block $s$). And $\sum_{t: \varepsilon_t=1, v_t^{(s)}\neq 0} w_t = r$.

**If $q_s = 0$**: All B-block-$s$ contributions from lifted terms must cancel: $\sum_{\varepsilon_t=1} v_t^{(s)} \otimes w_t = 0$.

### Coupling with core equations

Core slices assigned to B-block 1: slices 0 ($a_{01}$), 3 ($a_{11}$), 6 ($a_{21}$).
Core slices assigned to B-block 2: slices 1 ($a_{02}$), 4 ($a_{12}$), 7 ($a_{22}$).
Core slices assigned to B-block 0: slices 2 ($a_{10}$), 5 ($a_{20}$).

For slice $s$ with assigned block $(j_s, i_s)$, the core equation in the assigned block is:
$$\sum_{t \in T_s} v_t^{(j_s)} \otimes w_t^{(i_s)} = I_3$$

The lifted terms in $T_s$ contribute $v_t^{(j_s)} \otimes w_t^{(i_s)}$. By the B-block constraint:
- If $j_s \in \{1,2\}$ and $q_{j_s} \neq 0$: lifted terms share direction $q_{j_s}$ in B-block $j_s$, giving rank-≤1 total contribution. Non-lifted terms must carry ≥ rank 2 of $I_3$.
- If $j_s \in \{1,2\}$ and $q_{j_s} = 0$: lifted terms' B-block contributions cancel, so they contribute zero to the assigned block. Non-lifted terms must produce full $I_3$.

### The 28 most favorable cases

$\Delta$ has rank 2, supported only in block (0,0): $\Delta = I_3 + q_0 \otimes r_0$ with $q_0 \cdot r_0 = 1$.

For these: $q_1 = q_2 = r_1 = r_2 = 0$, so $q \otimes r$ is confined to block (0,0).

All 8 off-diagonal block sums vanish: lifted terms must produce $\Delta$ entirely in block (0,0).

**Necessary condition**: All lifted terms with nonzero B-block-1 or B-block-2 component must have these components cancel in sum. Same for C-blocks 1 and 2.

**Strongest form**: If all lifted terms are "block-(0,0)-confined" ($v_t \in \mathbb{F}_2^3 \times 0 \times 0$, $w_t \in \mathbb{F}_2^3 \times 0 \times 0$), then they contribute NOTHING to any assigned core block (since all assigned blocks have $j_s \neq 0$ or $i_s \neq 0$). Non-lifted terms alone must produce all 8 copies of $I_3$.

## Lower-Bound Route Summary

To prove $R_{\mathbb{F}_2}(T) \geq 21$, we must show: no 20-term decomposition exists.

**Complete logical chain**:
1. Any rank-20 decomposition has a rank-1 A-factor → DRAT-proved (research_record analysis)
2. Normalize to $E_{00}$ → gives rank-19 E11 core + lift bits
3. Lift condition: $\mathrm{rank}(M_0 + \Delta) \leq 1$ must hold
4. **If no rank-19 core CPD + ε-assignment satisfies (3) → rank ≥ 21**

This is a finite algebraic problem over $\mathbb{F}_2$ with ~530 binary variables and ~730 quadratic/bilinear constraints.

## Upper-Bound Route Summary

To prove $R_{\mathbb{F}_2}(T) \leq 22$: find any rank-19 E11 core CPD.

**Independent of lift condition**: the lift formula automatically gives rank 22.

The core has 19 × (8+9+9) = 494 binary unknowns and 648 Brent equations.

## SAT Encoding Plan

**Encoding A (lower bound)**: Encode the combined core + lift system.
- 19 terms: $u_t$ (8 bits), $v_t$ (9 bits), $w_t$ (9 bits), $\varepsilon_t$ (1 bit) = 513
- Target: $q$ (9 bits), $r$ (9 bits) = 18
- Total base: 531 variables + Tseytin auxiliary variables
- Core equations (648) + lift equations (81) + auxiliary clauses
- Symmetry breaking: fix one A-factor, ordering constraints
- UNSAT → rank ≥ 21

**Encoding B (upper bound)**: Encode core-only Brent equations.
- 19 terms: $u_t$ (8 bits), $v_t$ (9 bits), $w_t$ (9 bits) = 494
- Core equations (648) + auxiliary clauses
- SAT → rank ≤ 22

**Encoding C (hybrid, case split)**: For each of 28 rank-2 targets:
- Fix $(q_0, r_0)$ with $q_0 \cdot r_0 = 1$ and $q_1=q_2=r_1=r_2=0$
- Encode: core + fixed $\Delta$ = $I_3 + q_0 \otimes r_0$ in block (0,0)
- Each instance has fewer free variables and stronger propagation
- If ALL 28 are UNSAT → partial progress (still need other target cases)

## Files

- Bridge verification: [bridge_verification.json](../results/e11_bridge/bridge_verification.json)
- Core tensor: [e11_core_8x9x9.npy](../arrays/e11_bridge/e11_core_8x9x9.npy)
- Full tensor: [t333_9x9x9.npy](../arrays/e11_bridge/t333_9x9x9.npy)
- Lift obstruction analysis: [lift_obstruction_analysis.json](../results/lift_obstruction/lift_obstruction_analysis.json)
- Bridge verify script: [e11_bridge_verify.py](../code/e11_bridge_verify.py)
- Lift analysis script: [lift_obstruction_analysis.py](../code/lift_obstruction_analysis.py)

## Open Questions

1. **Tightness**: Can the B-block rank-1 constraint + core equations rule out all 262,144 target cases?
2. **Case reduction**: How many distinct target classes exist under the E11 stabilizer group?
3. **Tractability**: Is the combined SAT encoding tractable for modern solvers (CaDiCaL/Kissat)?
4. **Alternative**: Can algebraic arguments eliminate large classes of targets without SAT?
5. **Calibration**: What fraction of "generic" rank-19 8×9×9 CPDs (if they exist) admit the lift condition?
