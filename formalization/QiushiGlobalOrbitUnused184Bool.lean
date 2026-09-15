import QiushiGlobalOrbitUnused184SectionAll
import QiushiGlobalOrbitUnused184DeadAll
import QiushiGlobalOrbitUnused184SourceAll
import QiushiGlobalOrbitUnused184DeadSourceAll
import QiushiGlobalOrbitUnused184IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane184UnusedGenBool : PlaneExtBool plane184UnusedGenConfig where
  hSectionCoset := plane184UnusedGenSectionAll
  hDeadCover := plane184UnusedGenDeadAll
  hPlaneLeSource := plane184UnusedGenSourceAll
  hPlaneLeDead := plane184UnusedGenDeadSourceAll
  hIndicator := plane184UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
