import QiushiStep136Orbit435Defs

set_option maxHeartbeats 400000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
open BigOperators Finset Matrix Classical
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

theorem o435ScalarCoverage_state_16 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 0 0 0 0 1 0 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_17 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 1 0 0 0 1 0 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_18 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 0 1 0 0 1 0 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_19 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 1 1 0 0 1 0 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_20 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 0 0 1 0 1 0 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_21 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 1 0 1 0 1 0 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_22 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 0 1 1 0 1 0 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_23 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 1 1 1 0 1 0 = true then o435Lambda i else 0 := by
  decide

end QiushiMatmul
end
