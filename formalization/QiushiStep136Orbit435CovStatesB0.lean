import QiushiStep136Orbit435Defs

set_option maxHeartbeats 400000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
open BigOperators Finset Matrix Classical
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

theorem o435ScalarCoverage_state_0 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 0 0 0 0 0 0 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_1 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 1 0 0 0 0 0 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_2 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 0 1 0 0 0 0 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_3 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 1 1 0 0 0 0 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_4 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 0 0 1 0 0 0 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_5 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 1 0 1 0 0 0 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_6 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 0 1 1 0 0 0 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_7 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 1 1 1 0 0 0 = true then o435Lambda i else 0 := by
  decide

end QiushiMatmul
end
