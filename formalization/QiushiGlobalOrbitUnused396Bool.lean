import QiushiGlobalOrbitUnused396SectionAll
import QiushiGlobalOrbitUnused396DeadAll
import QiushiGlobalOrbitUnused396SourceAll
import QiushiGlobalOrbitUnused396DeadSourceAll
import QiushiGlobalOrbitUnused396IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane396UnusedGenBool : PlaneExtBool plane396UnusedGenConfig where
  hSectionCoset := plane396UnusedGenSectionAll
  hDeadCover := plane396UnusedGenDeadAll
  hPlaneLeSource := plane396UnusedGenSourceAll
  hPlaneLeDead := plane396UnusedGenDeadSourceAll
  hIndicator := plane396UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
