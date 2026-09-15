import QiushiGlobalOrbitUnused92SectionAll
import QiushiGlobalOrbitUnused92DeadAll
import QiushiGlobalOrbitUnused92SourceAll
import QiushiGlobalOrbitUnused92DeadSourceAll
import QiushiGlobalOrbitUnused92IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane92UnusedGenBool : PlaneExtBool plane92UnusedGenConfig where
  hSectionCoset := plane92UnusedGenSectionAll
  hDeadCover := plane92UnusedGenDeadAll
  hPlaneLeSource := plane92UnusedGenSourceAll
  hPlaneLeDead := plane92UnusedGenDeadSourceAll
  hIndicator := plane92UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
