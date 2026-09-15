import QiushiGlobalOrbitUnused305SectionAll
import QiushiGlobalOrbitUnused305DeadAll
import QiushiGlobalOrbitUnused305SourceAll
import QiushiGlobalOrbitUnused305DeadSourceAll
import QiushiGlobalOrbitUnused305IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane305UnusedGenBool : PlaneExtBool plane305UnusedGenConfig where
  hSectionCoset := plane305UnusedGenSectionAll
  hDeadCover := plane305UnusedGenDeadAll
  hPlaneLeSource := plane305UnusedGenSourceAll
  hPlaneLeDead := plane305UnusedGenDeadSourceAll
  hIndicator := plane305UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
