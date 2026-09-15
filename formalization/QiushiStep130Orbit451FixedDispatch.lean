import QiushiStep129Orbit451CovStatesB0
import QiushiStep129Orbit451CovStatesB1
import QiushiStep129Orbit451CovStatesB2
import QiushiStep129Orbit451CovStatesB3
import QiushiStep129Orbit451CovStatesB4
import QiushiStep129Orbit451CovStatesB5
import QiushiStep129Orbit451CovStatesB6
import QiushiStep129Orbit451CovStatesB7

set_option maxHeartbeats 200000
set_option linter.unusedVariables false
open BigOperators Finset Matrix
namespace QiushiMatmul

/-- Weighted coverage over all 64 scalar states, proved by applying the
    pre-compiled per-state theorems.

    **Key fix:** The `fin_cases` order is reversed to x5, x4, ..., x0 so that
    goal k corresponds exactly to `o451ScalarCoverage_state_k`.
    With the old order `x0, x1, ..., x5`, goal 1 is `(0,0,0,0,0,1)` = state 32,
    causing Lean to normalize 44-term sums to reconcile the mismatch. -/
theorem o451ScalarCoverage :
    ∀ (x0 x1 x2 x3 x4 x5 : F2), 40 ≤
      ∑ i : Fin 44, if o451ScalarCoverB i x0 x1 x2 x3 x4 x5 = true then o451Lambda i else 0 := by
  intro x0 x1 x2 x3 x4 x5
  fin_cases x5 <;> fin_cases x4 <;> fin_cases x3 <;> fin_cases x2 <;> fin_cases x1 <;> fin_cases x0
  · exact o451ScalarCoverage_state_0
  · exact o451ScalarCoverage_state_1
  · exact o451ScalarCoverage_state_2
  · exact o451ScalarCoverage_state_3
  · exact o451ScalarCoverage_state_4
  · exact o451ScalarCoverage_state_5
  · exact o451ScalarCoverage_state_6
  · exact o451ScalarCoverage_state_7
  · exact o451ScalarCoverage_state_8
  · exact o451ScalarCoverage_state_9
  · exact o451ScalarCoverage_state_10
  · exact o451ScalarCoverage_state_11
  · exact o451ScalarCoverage_state_12
  · exact o451ScalarCoverage_state_13
  · exact o451ScalarCoverage_state_14
  · exact o451ScalarCoverage_state_15
  · exact o451ScalarCoverage_state_16
  · exact o451ScalarCoverage_state_17
  · exact o451ScalarCoverage_state_18
  · exact o451ScalarCoverage_state_19
  · exact o451ScalarCoverage_state_20
  · exact o451ScalarCoverage_state_21
  · exact o451ScalarCoverage_state_22
  · exact o451ScalarCoverage_state_23
  · exact o451ScalarCoverage_state_24
  · exact o451ScalarCoverage_state_25
  · exact o451ScalarCoverage_state_26
  · exact o451ScalarCoverage_state_27
  · exact o451ScalarCoverage_state_28
  · exact o451ScalarCoverage_state_29
  · exact o451ScalarCoverage_state_30
  · exact o451ScalarCoverage_state_31
  · exact o451ScalarCoverage_state_32
  · exact o451ScalarCoverage_state_33
  · exact o451ScalarCoverage_state_34
  · exact o451ScalarCoverage_state_35
  · exact o451ScalarCoverage_state_36
  · exact o451ScalarCoverage_state_37
  · exact o451ScalarCoverage_state_38
  · exact o451ScalarCoverage_state_39
  · exact o451ScalarCoverage_state_40
  · exact o451ScalarCoverage_state_41
  · exact o451ScalarCoverage_state_42
  · exact o451ScalarCoverage_state_43
  · exact o451ScalarCoverage_state_44
  · exact o451ScalarCoverage_state_45
  · exact o451ScalarCoverage_state_46
  · exact o451ScalarCoverage_state_47
  · exact o451ScalarCoverage_state_48
  · exact o451ScalarCoverage_state_49
  · exact o451ScalarCoverage_state_50
  · exact o451ScalarCoverage_state_51
  · exact o451ScalarCoverage_state_52
  · exact o451ScalarCoverage_state_53
  · exact o451ScalarCoverage_state_54
  · exact o451ScalarCoverage_state_55
  · exact o451ScalarCoverage_state_56
  · exact o451ScalarCoverage_state_57
  · exact o451ScalarCoverage_state_58
  · exact o451ScalarCoverage_state_59
  · exact o451ScalarCoverage_state_60
  · exact o451ScalarCoverage_state_61
  · exact o451ScalarCoverage_state_62
  · exact o451ScalarCoverage_state_63

end QiushiMatmul
