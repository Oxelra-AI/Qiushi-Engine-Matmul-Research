import QiushiStep136Orbit435CovStatesB0
import QiushiStep136Orbit435CovStatesB1
import QiushiStep136Orbit435CovStatesB2
import QiushiStep136Orbit435CovStatesB3
import QiushiStep136Orbit435CovStatesB4
import QiushiStep136Orbit435CovStatesB5
import QiushiStep136Orbit435CovStatesB6
import QiushiStep136Orbit435CovStatesB7

set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
open BigOperators Finset Matrix
namespace QiushiMatmul

theorem o435ScalarCoverage :
    ∀ (x0 x1 x2 x3 x4 x5 : F2), 12158280 ≤
      ∑ i : Fin 63, if o435ScalarCoverB i x0 x1 x2 x3 x4 x5 = true then o435Lambda i else 0 := by
  intro x0 x1 x2 x3 x4 x5
  fin_cases x5 <;> fin_cases x4 <;> fin_cases x3 <;> fin_cases x2 <;> fin_cases x1 <;> fin_cases x0
  · exact o435ScalarCoverage_state_0
  · exact o435ScalarCoverage_state_1
  · exact o435ScalarCoverage_state_2
  · exact o435ScalarCoverage_state_3
  · exact o435ScalarCoverage_state_4
  · exact o435ScalarCoverage_state_5
  · exact o435ScalarCoverage_state_6
  · exact o435ScalarCoverage_state_7
  · exact o435ScalarCoverage_state_8
  · exact o435ScalarCoverage_state_9
  · exact o435ScalarCoverage_state_10
  · exact o435ScalarCoverage_state_11
  · exact o435ScalarCoverage_state_12
  · exact o435ScalarCoverage_state_13
  · exact o435ScalarCoverage_state_14
  · exact o435ScalarCoverage_state_15
  · exact o435ScalarCoverage_state_16
  · exact o435ScalarCoverage_state_17
  · exact o435ScalarCoverage_state_18
  · exact o435ScalarCoverage_state_19
  · exact o435ScalarCoverage_state_20
  · exact o435ScalarCoverage_state_21
  · exact o435ScalarCoverage_state_22
  · exact o435ScalarCoverage_state_23
  · exact o435ScalarCoverage_state_24
  · exact o435ScalarCoverage_state_25
  · exact o435ScalarCoverage_state_26
  · exact o435ScalarCoverage_state_27
  · exact o435ScalarCoverage_state_28
  · exact o435ScalarCoverage_state_29
  · exact o435ScalarCoverage_state_30
  · exact o435ScalarCoverage_state_31
  · exact o435ScalarCoverage_state_32
  · exact o435ScalarCoverage_state_33
  · exact o435ScalarCoverage_state_34
  · exact o435ScalarCoverage_state_35
  · exact o435ScalarCoverage_state_36
  · exact o435ScalarCoverage_state_37
  · exact o435ScalarCoverage_state_38
  · exact o435ScalarCoverage_state_39
  · exact o435ScalarCoverage_state_40
  · exact o435ScalarCoverage_state_41
  · exact o435ScalarCoverage_state_42
  · exact o435ScalarCoverage_state_43
  · exact o435ScalarCoverage_state_44
  · exact o435ScalarCoverage_state_45
  · exact o435ScalarCoverage_state_46
  · exact o435ScalarCoverage_state_47
  · exact o435ScalarCoverage_state_48
  · exact o435ScalarCoverage_state_49
  · exact o435ScalarCoverage_state_50
  · exact o435ScalarCoverage_state_51
  · exact o435ScalarCoverage_state_52
  · exact o435ScalarCoverage_state_53
  · exact o435ScalarCoverage_state_54
  · exact o435ScalarCoverage_state_55
  · exact o435ScalarCoverage_state_56
  · exact o435ScalarCoverage_state_57
  · exact o435ScalarCoverage_state_58
  · exact o435ScalarCoverage_state_59
  · exact o435ScalarCoverage_state_60
  · exact o435ScalarCoverage_state_61
  · exact o435ScalarCoverage_state_62
  · exact o435ScalarCoverage_state_63

end QiushiMatmul
