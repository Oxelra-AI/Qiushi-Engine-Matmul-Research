import QiushiGlobalOrbitUnused386SectionAll
import QiushiGlobalOrbitUnused386DeadAll
import QiushiGlobalOrbitUnused386SourceAll
import QiushiGlobalOrbitUnused386DeadSourceAll
import QiushiGlobalOrbitUnused386IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane386UnusedGenBool : PlaneExtBool plane386UnusedGenConfig where
  hSectionCoset := plane386UnusedGenSectionAll
  hDeadCover := plane386UnusedGenDeadAll
  hPlaneLeSource := plane386UnusedGenSourceAll
  hPlaneLeDead := plane386UnusedGenDeadSourceAll
  hIndicator := plane386UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
