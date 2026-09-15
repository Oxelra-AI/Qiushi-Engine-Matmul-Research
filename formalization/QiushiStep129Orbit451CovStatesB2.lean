import QiushiStep128Orbit451Defs

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
open BigOperators Finset Matrix Classical
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

theorem o451ScalarCoverage_state_16 :
    40 ≤ ∑ i : Fin 44, if o451ScalarCoverB i 0 0 0 0 1 0 = true then o451Lambda i else 0 := by
  decide

theorem o451ScalarCoverage_state_17 :
    40 ≤ ∑ i : Fin 44, if o451ScalarCoverB i 1 0 0 0 1 0 = true then o451Lambda i else 0 := by
  decide

theorem o451ScalarCoverage_state_18 :
    40 ≤ ∑ i : Fin 44, if o451ScalarCoverB i 0 1 0 0 1 0 = true then o451Lambda i else 0 := by
  decide

theorem o451ScalarCoverage_state_19 :
    40 ≤ ∑ i : Fin 44, if o451ScalarCoverB i 1 1 0 0 1 0 = true then o451Lambda i else 0 := by
  decide

theorem o451ScalarCoverage_state_20 :
    40 ≤ ∑ i : Fin 44, if o451ScalarCoverB i 0 0 1 0 1 0 = true then o451Lambda i else 0 := by
  decide

theorem o451ScalarCoverage_state_21 :
    40 ≤ ∑ i : Fin 44, if o451ScalarCoverB i 1 0 1 0 1 0 = true then o451Lambda i else 0 := by
  decide

theorem o451ScalarCoverage_state_22 :
    40 ≤ ∑ i : Fin 44, if o451ScalarCoverB i 0 1 1 0 1 0 = true then o451Lambda i else 0 := by
  decide

theorem o451ScalarCoverage_state_23 :
    40 ≤ ∑ i : Fin 44, if o451ScalarCoverB i 1 1 1 0 1 0 = true then o451Lambda i else 0 := by
  decide

end QiushiMatmul
end
