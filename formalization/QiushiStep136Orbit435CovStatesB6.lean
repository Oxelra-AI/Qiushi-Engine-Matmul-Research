import QiushiStep136Orbit435Defs

set_option maxHeartbeats 400000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
open BigOperators Finset Matrix Classical
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

theorem o435ScalarCoverage_state_48 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 0 0 0 0 1 1 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_49 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 1 0 0 0 1 1 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_50 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 0 1 0 0 1 1 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_51 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 1 1 0 0 1 1 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_52 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 0 0 1 0 1 1 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_53 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 1 0 1 0 1 1 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_54 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 0 1 1 0 1 1 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_55 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 1 1 1 0 1 1 = true then o435Lambda i else 0 := by
  decide

end QiushiMatmul
end
