import QiushiStep136Orbit435Defs

set_option maxHeartbeats 400000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
open BigOperators Finset Matrix Classical
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

theorem o435ScalarCoverage_state_40 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 0 0 0 1 0 1 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_41 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 1 0 0 1 0 1 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_42 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 0 1 0 1 0 1 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_43 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 1 1 0 1 0 1 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_44 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 0 0 1 1 0 1 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_45 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 1 0 1 1 0 1 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_46 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 0 1 1 1 0 1 = true then o435Lambda i else 0 := by
  decide

theorem o435ScalarCoverage_state_47 :
    12158280 ≤ ∑ i : Fin 63, if o435ScalarCoverB i 1 1 1 1 0 1 = true then o435Lambda i else 0 := by
  decide

end QiushiMatmul
end
