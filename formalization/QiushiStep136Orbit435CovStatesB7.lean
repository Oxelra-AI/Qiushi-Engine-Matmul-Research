import QiushiStep136Orbit435Defs

set_option maxHeartbeats 400000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
open BigOperators Finset Matrix Classical
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

theorem o435ScalarCoverage_state_56 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 0 0 0 1 1 1 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_57 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 1 0 0 1 1 1 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_58 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 0 1 0 1 1 1 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_59 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 1 1 0 1 1 1 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_60 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 0 0 1 1 1 1 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_61 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 1 0 1 1 1 1 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_62 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 0 1 1 1 1 1 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_63 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 1 1 1 1 1 1 = true then o435Lambda i else 0 := by
  decide

end QiushiMatmul
end
