import QiushiGlobalOrbitUnused308SectionAll
import QiushiGlobalOrbitUnused308DeadAll
import QiushiGlobalOrbitUnused308SourceAll
import QiushiGlobalOrbitUnused308DeadSourceAll
import QiushiGlobalOrbitUnused308IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane308UnusedGenBool : PlaneExtBool plane308UnusedGenConfig where
  hSectionCoset := plane308UnusedGenSectionAll
  hDeadCover := plane308UnusedGenDeadAll
  hPlaneLeSource := plane308UnusedGenSourceAll
  hPlaneLeDead := plane308UnusedGenDeadSourceAll
  hIndicator := plane308UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
