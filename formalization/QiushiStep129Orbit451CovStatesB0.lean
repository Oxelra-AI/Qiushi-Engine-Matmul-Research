import QiushiStep128Orbit451Defs

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
open BigOperators Finset Matrix Classical
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

theorem o451ScalarCoverage_state_0 :
    40 ≤ ∑ i : Fin 44, if o451ScalarCoverB i 0 0 0 0 0 0 = true then o451Lambda i else 0 := by
  decide

theorem o451ScalarCoverage_state_1 :
    40 ≤ ∑ i : Fin 44, if o451ScalarCoverB i 1 0 0 0 0 0 = true then o451Lambda i else 0 := by
  decide

theorem o451ScalarCoverage_state_2 :
    40 ≤ ∑ i : Fin 44, if o451ScalarCoverB i 0 1 0 0 0 0 = true then o451Lambda i else 0 := by
  decide

theorem o451ScalarCoverage_state_3 :
    40 ≤ ∑ i : Fin 44, if o451ScalarCoverB i 1 1 0 0 0 0 = true then o451Lambda i else 0 := by
  decide

theorem o451ScalarCoverage_state_4 :
    40 ≤ ∑ i : Fin 44, if o451ScalarCoverB i 0 0 1 0 0 0 = true then o451Lambda i else 0 := by
  decide

theorem o451ScalarCoverage_state_5 :
    40 ≤ ∑ i : Fin 44, if o451ScalarCoverB i 1 0 1 0 0 0 = true then o451Lambda i else 0 := by
  decide

theorem o451ScalarCoverage_state_6 :
    40 ≤ ∑ i : Fin 44, if o451ScalarCoverB i 0 1 1 0 0 0 = true then o451Lambda i else 0 := by
  decide

theorem o451ScalarCoverage_state_7 :
    40 ≤ ∑ i : Fin 44, if o451ScalarCoverB i 1 1 1 0 0 0 = true then o451Lambda i else 0 := by
  decide

end QiushiMatmul
end
