import QiushiGlobalOrbitUnused289SectionAll
import QiushiGlobalOrbitUnused289DeadAll
import QiushiGlobalOrbitUnused289SourceAll
import QiushiGlobalOrbitUnused289DeadSourceAll
import QiushiGlobalOrbitUnused289IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane289UnusedGenBool : PlaneExtBool plane289UnusedGenConfig where
  hSectionCoset := plane289UnusedGenSectionAll
  hDeadCover := plane289UnusedGenDeadAll
  hPlaneLeSource := plane289UnusedGenSourceAll
  hPlaneLeDead := plane289UnusedGenDeadSourceAll
  hIndicator := plane289UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
