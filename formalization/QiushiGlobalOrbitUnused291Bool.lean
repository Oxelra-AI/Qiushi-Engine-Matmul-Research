import QiushiGlobalOrbitUnused291SectionAll
import QiushiGlobalOrbitUnused291DeadAll
import QiushiGlobalOrbitUnused291SourceAll
import QiushiGlobalOrbitUnused291DeadSourceAll
import QiushiGlobalOrbitUnused291IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane291UnusedGenBool : PlaneExtBool plane291UnusedGenConfig where
  hSectionCoset := plane291UnusedGenSectionAll
  hDeadCover := plane291UnusedGenDeadAll
  hPlaneLeSource := plane291UnusedGenSourceAll
  hPlaneLeDead := plane291UnusedGenDeadSourceAll
  hIndicator := plane291UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
