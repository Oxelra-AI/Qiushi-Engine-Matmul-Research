import QiushiGlobalOrbitUnused383SectionAll
import QiushiGlobalOrbitUnused383DeadAll
import QiushiGlobalOrbitUnused383SourceAll
import QiushiGlobalOrbitUnused383DeadSourceAll
import QiushiGlobalOrbitUnused383IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane383UnusedGenBool : PlaneExtBool plane383UnusedGenConfig where
  hSectionCoset := plane383UnusedGenSectionAll
  hDeadCover := plane383UnusedGenDeadAll
  hPlaneLeSource := plane383UnusedGenSourceAll
  hPlaneLeDead := plane383UnusedGenDeadSourceAll
  hIndicator := plane383UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
