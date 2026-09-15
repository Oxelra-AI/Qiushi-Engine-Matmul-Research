import QiushiGlobalOrbitUnused248SectionAll
import QiushiGlobalOrbitUnused248DeadAll
import QiushiGlobalOrbitUnused248SourceAll
import QiushiGlobalOrbitUnused248DeadSourceAll
import QiushiGlobalOrbitUnused248IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane248UnusedGenBool : PlaneExtBool plane248UnusedGenConfig where
  hSectionCoset := plane248UnusedGenSectionAll
  hDeadCover := plane248UnusedGenDeadAll
  hPlaneLeSource := plane248UnusedGenSourceAll
  hPlaneLeDead := plane248UnusedGenDeadSourceAll
  hIndicator := plane248UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
