import QiushiStep128Orbit451Defs

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
open BigOperators Finset Matrix Classical
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

theorem o451ScalarCoverage_state_8 :
    40 ≤ ∑ i : Fin 44, if o451ScalarCoverB i 0 0 0 1 0 0 = true then o451Lambda i else 0 := by
  decide

theorem o451ScalarCoverage_state_9 :
    40 ≤ ∑ i : Fin 44, if o451ScalarCoverB i 1 0 0 1 0 0 = true then o451Lambda i else 0 := by
  decide

theorem o451ScalarCoverage_state_10 :
    40 ≤ ∑ i : Fin 44, if o451ScalarCoverB i 0 1 0 1 0 0 = true then o451Lambda i else 0 := by
  decide

theorem o451ScalarCoverage_state_11 :
    40 ≤ ∑ i : Fin 44, if o451ScalarCoverB i 1 1 0 1 0 0 = true then o451Lambda i else 0 := by
  decide

theorem o451ScalarCoverage_state_12 :
    40 ≤ ∑ i : Fin 44, if o451ScalarCoverB i 0 0 1 1 0 0 = true then o451Lambda i else 0 := by
  decide

theorem o451ScalarCoverage_state_13 :
    40 ≤ ∑ i : Fin 44, if o451ScalarCoverB i 1 0 1 1 0 0 = true then o451Lambda i else 0 := by
  decide

theorem o451ScalarCoverage_state_14 :
    40 ≤ ∑ i : Fin 44, if o451ScalarCoverB i 0 1 1 1 0 0 = true then o451Lambda i else 0 := by
  decide

theorem o451ScalarCoverage_state_15 :
    40 ≤ ∑ i : Fin 44, if o451ScalarCoverB i 1 1 1 1 0 0 = true then o451Lambda i else 0 := by
  decide

end QiushiMatmul
end
