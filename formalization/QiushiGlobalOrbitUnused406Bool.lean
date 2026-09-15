import QiushiGlobalOrbitUnused406SectionAll
import QiushiGlobalOrbitUnused406DeadAll
import QiushiGlobalOrbitUnused406SourceAll
import QiushiGlobalOrbitUnused406DeadSourceAll
import QiushiGlobalOrbitUnused406IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane406UnusedGenBool : PlaneExtBool plane406UnusedGenConfig where
  hSectionCoset := plane406UnusedGenSectionAll
  hDeadCover := plane406UnusedGenDeadAll
  hPlaneLeSource := plane406UnusedGenSourceAll
  hPlaneLeDead := plane406UnusedGenDeadSourceAll
  hIndicator := plane406UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
