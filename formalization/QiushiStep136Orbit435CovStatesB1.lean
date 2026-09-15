import QiushiStep136Orbit435Defs

set_option maxHeartbeats 400000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
open BigOperators Finset Matrix Classical
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

theorem o435ScalarCoverage_state_8 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 0 0 0 1 0 0 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_9 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 1 0 0 1 0 0 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_10 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 0 1 0 1 0 0 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_11 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 1 1 0 1 0 0 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_12 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 0 0 1 1 0 0 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_13 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 1 0 1 1 0 0 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_14 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 0 1 1 1 0 0 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_15 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 1 1 1 1 0 0 = true then o435Lambda i else 0 := by
  decide

end QiushiMatmul
end
