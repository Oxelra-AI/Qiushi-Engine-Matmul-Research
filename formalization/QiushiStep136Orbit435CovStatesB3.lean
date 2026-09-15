import QiushiStep136Orbit435Defs

set_option maxHeartbeats 400000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
open BigOperators Finset Matrix Classical
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

theorem o435ScalarCoverage_state_24 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 0 0 0 1 1 0 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_25 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 1 0 0 1 1 0 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_26 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 0 1 0 1 1 0 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_27 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 1 1 0 1 1 0 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_28 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 0 0 1 1 1 0 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_29 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 1 0 1 1 1 0 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_30 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 0 1 1 1 1 0 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_31 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 1 1 1 1 1 0 = true then o435Lambda i else 0 := by
  decide

end QiushiMatmul
end
