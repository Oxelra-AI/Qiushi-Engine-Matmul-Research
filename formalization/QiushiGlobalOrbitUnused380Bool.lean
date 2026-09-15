import QiushiGlobalOrbitUnused380SectionAll
import QiushiGlobalOrbitUnused380DeadAll
import QiushiGlobalOrbitUnused380SourceAll
import QiushiGlobalOrbitUnused380DeadSourceAll
import QiushiGlobalOrbitUnused380IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane380UnusedGenBool : PlaneExtBool plane380UnusedGenConfig where
  hSectionCoset := plane380UnusedGenSectionAll
  hDeadCover := plane380UnusedGenDeadAll
  hPlaneLeSource := plane380UnusedGenSourceAll
  hPlaneLeDead := plane380UnusedGenDeadSourceAll
  hIndicator := plane380UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
