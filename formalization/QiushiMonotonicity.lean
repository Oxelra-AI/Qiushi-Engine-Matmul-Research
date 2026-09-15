import Mathlib
import QiushiOccupationAPI
import QiushiTotalWeight

/-!
# Monotonicity and preceding-bound infrastructure for quotient tensor rank

Two reusable theorems for the dimension-graded derivation:

1. **Monotonicity**: W ≤ U → QuotientRankAtLeast U r → QuotientRankAtLeast W r
   (lower bounds propagate from superspaces to subspaces)

2. **Preceding-bound zero-fiber**: if R(T/W) ≥ r is already established,
   any length-r quotient decomposition has no terms with A_t ∈ W.
   This replaces the exit-subspace approach for intermediate derivation steps.
-/

set_option maxHeartbeats 4000000
open BigOperators Finset
namespace QiushiMatmul

-- ============================================================================
-- Monotonicity
-- ============================================================================

/-- Monotonicity: if W ≤ U, a lower bound at the superspace U
is also a lower bound at the subspace W.

Proof: any QuotientTensorDecomp W m with m < r can be further-quotiented
to T/U, contradicting QuotientRankAtLeast U r. -/
theorem quotientRankAtLeast_mono {W U : Submodule F2 Mat3}
    (hWU : W ≤ U) {r : ℕ} (h : QuotientRankAtLeast U r) :
    QuotientRankAtLeast W r :=
  quotientRankAtLeast_of_contradiction W r
    (fun _m hm D => quotient_bound_exceeds_length hWU D h hm)

-- ============================================================================
-- Preceding-bound zero fiber
-- ============================================================================

/-- If W itself has rank ≥ r, any length-r quotient decomposition has
killSet D W of size 0 (i.e., no terms lie in W).
Uses killSet_le_target with U = W, hWU = le_refl, m = target = r. -/
theorem zero_fiber_from_preceding_bound {W : Submodule F2 Mat3}
    {r : ℕ} (hW : QuotientRankAtLeast W r)
    (D : QuotientTensorDecomp W r) :
    (killSet D W).card = 0 := by
  have h := killSet_le_target (le_refl W) D hW le_rfl le_rfl
  omega

/-- The preceding bound also works for the coset-count formulation:
cosetCount D 0 = 0 when QuotientRankAtLeast W r. -/
theorem cosetCount_zero_from_preceding {W : Submodule F2 Mat3}
    {r : ℕ} (hW : QuotientRankAtLeast W r)
    (D : QuotientTensorDecomp W r) :
    cosetCount D (0 : Mat3) = 0 := by
  rw [cosetCount_zero_eq_killSet]
  exact zero_fiber_from_preceding_bound hW D

-- ============================================================================
-- Combination: monotonicity + total weight → nonzero fiber total
-- ============================================================================

/-- In a length-r quotient decomposition of T/W, if R(T/W) ≥ r (preceding bound),
then all r terms have nonzero quotient label. The nonzero fiber sum is exactly r. -/
theorem total_nonzero_from_preceding {W : Submodule F2 Mat3}
    {r : ℕ} (hW : QuotientRankAtLeast W r)
    (D : QuotientTensorDecomp W r) :
    r - cosetCount D 0 = r := by
  rw [cosetCount_zero_from_preceding hW D]
  omega

end QiushiMatmul
