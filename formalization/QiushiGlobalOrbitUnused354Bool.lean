import QiushiGlobalOrbitUnused354SectionAll
import QiushiGlobalOrbitUnused354DeadAll
import QiushiGlobalOrbitUnused354SourceAll
import QiushiGlobalOrbitUnused354DeadSourceAll
import QiushiGlobalOrbitUnused354IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane354UnusedGenBool : PlaneExtBool plane354UnusedGenConfig where
  hSectionCoset := plane354UnusedGenSectionAll
  hDeadCover := plane354UnusedGenDeadAll
  hPlaneLeSource := plane354UnusedGenSourceAll
  hPlaneLeDead := plane354UnusedGenDeadSourceAll
  hIndicator := plane354UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
