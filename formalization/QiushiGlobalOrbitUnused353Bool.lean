import QiushiGlobalOrbitUnused353SectionAll
import QiushiGlobalOrbitUnused353DeadAll
import QiushiGlobalOrbitUnused353SourceAll
import QiushiGlobalOrbitUnused353DeadSourceAll
import QiushiGlobalOrbitUnused353IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane353UnusedGenBool : PlaneExtBool plane353UnusedGenConfig where
  hSectionCoset := plane353UnusedGenSectionAll
  hDeadCover := plane353UnusedGenDeadAll
  hPlaneLeSource := plane353UnusedGenSourceAll
  hPlaneLeDead := plane353UnusedGenDeadSourceAll
  hIndicator := plane353UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
