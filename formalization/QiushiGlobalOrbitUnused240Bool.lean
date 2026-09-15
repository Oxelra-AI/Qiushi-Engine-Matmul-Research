import QiushiGlobalOrbitUnused240SectionAll
import QiushiGlobalOrbitUnused240DeadAll
import QiushiGlobalOrbitUnused240SourceAll
import QiushiGlobalOrbitUnused240DeadSourceAll
import QiushiGlobalOrbitUnused240IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane240UnusedGenBool : PlaneExtBool plane240UnusedGenConfig where
  hSectionCoset := plane240UnusedGenSectionAll
  hDeadCover := plane240UnusedGenDeadAll
  hPlaneLeSource := plane240UnusedGenSourceAll
  hPlaneLeDead := plane240UnusedGenDeadSourceAll
  hIndicator := plane240UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
