import QiushiGlobalOrbitUnused395SectionAll
import QiushiGlobalOrbitUnused395DeadAll
import QiushiGlobalOrbitUnused395SourceAll
import QiushiGlobalOrbitUnused395DeadSourceAll
import QiushiGlobalOrbitUnused395IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane395UnusedGenBool : PlaneExtBool plane395UnusedGenConfig where
  hSectionCoset := plane395UnusedGenSectionAll
  hDeadCover := plane395UnusedGenDeadAll
  hPlaneLeSource := plane395UnusedGenSourceAll
  hPlaneLeDead := plane395UnusedGenDeadSourceAll
  hIndicator := plane395UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
