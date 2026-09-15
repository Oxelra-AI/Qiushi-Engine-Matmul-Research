import QiushiGlobalOrbitUnused407SectionAll
import QiushiGlobalOrbitUnused407DeadAll
import QiushiGlobalOrbitUnused407SourceAll
import QiushiGlobalOrbitUnused407DeadSourceAll
import QiushiGlobalOrbitUnused407IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane407UnusedGenBool : PlaneExtBool plane407UnusedGenConfig where
  hSectionCoset := plane407UnusedGenSectionAll
  hDeadCover := plane407UnusedGenDeadAll
  hPlaneLeSource := plane407UnusedGenSourceAll
  hPlaneLeDead := plane407UnusedGenDeadSourceAll
  hIndicator := plane407UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
