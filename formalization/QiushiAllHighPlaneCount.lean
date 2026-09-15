import QiushiAllHighCountBridge
import QiushiAllHighCountRows

namespace QiushiMatmul.AllHighCount

theorem eligible_code_pair_count : Nat.card EligibleCodePairs = 192108 :=
  eligible_code_count_eq_rows.trans eligible_row_total

theorem high_pair_count : Nat.card HighPairs = 192108 := by
  rw [← Nat.card_congr eligibleCodeEquiv]
  exact eligible_code_pair_count

/-- Exact count of actual all-high matrix planes; no orbit-uniqueness assertion. -/
theorem all_high_plane_count :
    Nat.card {W : Submodule F2 Mat3 // Module.finrank F2 W = 2 ∧
      ∀ A ∈ W, A ≠ 0 → 2 ≤ A.rank} = 32018 := by
  change Nat.card HighPlanes = 32018
  have h := high_pair_count_eq_six_mul_planes
  rw [high_pair_count] at h
  omega

end QiushiMatmul.AllHighCount
