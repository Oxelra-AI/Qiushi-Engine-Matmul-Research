import QiushiGlobalOrbitUnused388SectionAll
import QiushiGlobalOrbitUnused388DeadAll
import QiushiGlobalOrbitUnused388SourceAll
import QiushiGlobalOrbitUnused388DeadSourceAll
import QiushiGlobalOrbitUnused388IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane388UnusedGenBool : PlaneExtBool plane388UnusedGenConfig where
  hSectionCoset := plane388UnusedGenSectionAll
  hDeadCover := plane388UnusedGenDeadAll
  hPlaneLeSource := plane388UnusedGenSourceAll
  hPlaneLeDead := plane388UnusedGenDeadSourceAll
  hIndicator := plane388UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
