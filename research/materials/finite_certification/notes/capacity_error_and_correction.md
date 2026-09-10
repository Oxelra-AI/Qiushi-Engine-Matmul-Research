# Capacity Feasibility — Critical Error Found and Corrected

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Core Mathematical Structure

The Wang capacity constraints for the E11 core work as follows:

For a rank-s decomposition of core_E11 = Σ_{t=1}^s a_t ⊗ b_t ⊗ c_t (where a_t ∈ F₂⁸):

**For each nonzero vector p ∈ F₂⁸ (equivalently, each functional φ_p on F₂⁸):**
- The restriction of core to ker(φ_p) = {a : <p, a> = 0} has F₂ rank ≥ L_p
- Terms contributing to this restriction are those with a_t ≠ p (and a_t ≠ 0)
- Because: term t contributes zero to core|_{ker(φ_p)} iff a_t ∈ span{p}\{0} = {p}
- Therefore: #{t : a_t = p} ≤ s - L_p

**This is a MULTIPLICITY constraint on individual points, NOT a halfspace constraint!**

## The Error

The initial ILP encoded: #{t : <f, a_t> = 1} ≤ s - L_f (counting all points in a 128-point halfspace).
The CORRECT constraint is: #{t : a_t = f} ≤ s - L_f (counting only the single point f).

The halfspace constraint is enormously overconstrained compared to the correct point-multiplicity constraint. This is why the ILP reported INFEASIBLE for all ranks 19-23 — those results are INVALID.

## LB Classification (correct, verified)

- 24 functionals at Wang LB = 17 (rank-1 matrices touching e₁): multiplicity ≤ s-17
- 231 functionals at Wang LB = 18 (all others): multiplicity ≤ s-18

For s = 19: cap = 2 (LB-17) or 1 (LB-18). With 255 available points, this is TRIVIALLY FEASIBLE using dim-2 constraints alone.

## What's Needed: Higher-Dimensional Constraints

The dim-2 (hyperplane) constraints alone can't obstruct rank 19 because they only limit individual point multiplicities. The real power comes from higher-dimensional Wang orbits:

For a dim-(k+1) orbit [E11, f₁, ..., fₖ] with lower bound L:
- #{t : a_t ∈ span{f₁,...,fₖ}\{0}} ≤ s - L
- This constrains the total multiplicity of 2^k - 1 points

To determine feasibility, we need ALL 496 Wang orbits parsed and translated to F₂⁸ constraints. The dim-3 through dim-8 orbits (with up to 7-127 point subset constraints and potentially low LBs) can jointly constrain the packing much more tightly.

## cn122 Verification

The cn122 restriction to E11 core has 21 effective terms (23 - 2 pure-E11):
- 10 terms with a₁₁ = 0, 11 terms with a₁₁ = 1 (but nonzero projection)
- 18 distinct 8-bit A-factors, max multiplicity 2
- Factor multiplicities: {18:2, 32:2, 128:2}, rest singleton

## Next Steps

1. Re-parse the FULL Wang certificate (all 496 orbits) to get every orbit containing E11
2. For each such orbit, translate its constraints to F₂⁸ subspace packing constraints
3. Build the CORRECT ILP with all subspace multiplicity constraints
4. Solve for s = 19, 20, 21 — this determines whether Wang's table alone can raise the core LB
5. If feasible: need Wang-style backtracking on the core, or different approach
6. If infeasible: new F₂ lower bound; verify by independent route

## Key Files
- [capacity_feasibility_v2.py](../../occupation_and_completion/code/capacity_feasibility_v2.py): WRONG halfspace encoding (INVALID results)
- [check_cn122_constraints.py](../../exact_baselines/code/check_cn122_constraints.py): cn122 diagnostic (correct)
- [capacity_feasibility_corrected.json](../../occupation_and_completion/results/restricted_cores/capacity_feasibility_corrected.json): INVALID (wrong constraints)
- Wang certificate: [cert_profile.json](../../quotient_cores/results/wang_f2_lb20/cert_profile.json) (only has dim 0-2 orbits)
- Need: full 496-orbit parse with constraint values and LBs
