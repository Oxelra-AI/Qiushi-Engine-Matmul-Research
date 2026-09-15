import QiushiGlobalOrbitUnused404SectionAll
import QiushiGlobalOrbitUnused404DeadAll
import QiushiGlobalOrbitUnused404SourceAll
import QiushiGlobalOrbitUnused404DeadSourceAll
import QiushiGlobalOrbitUnused404IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane404UnusedGenBool : PlaneExtBool plane404UnusedGenConfig where
  hSectionCoset := plane404UnusedGenSectionAll
  hDeadCover := plane404UnusedGenDeadAll
  hPlaneLeSource := plane404UnusedGenSourceAll
  hPlaneLeDead := plane404UnusedGenDeadSourceAll
  hIndicator := plane404UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
