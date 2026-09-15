import QiushiGlobalOrbitUnused376SectionAll
import QiushiGlobalOrbitUnused376DeadAll
import QiushiGlobalOrbitUnused376SourceAll
import QiushiGlobalOrbitUnused376DeadSourceAll
import QiushiGlobalOrbitUnused376IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane376UnusedGenBool : PlaneExtBool plane376UnusedGenConfig where
  hSectionCoset := plane376UnusedGenSectionAll
  hDeadCover := plane376UnusedGenDeadAll
  hPlaneLeSource := plane376UnusedGenSourceAll
  hPlaneLeDead := plane376UnusedGenDeadSourceAll
  hIndicator := plane376UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
