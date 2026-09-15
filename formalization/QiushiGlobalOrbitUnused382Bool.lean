import QiushiGlobalOrbitUnused382SectionAll
import QiushiGlobalOrbitUnused382DeadAll
import QiushiGlobalOrbitUnused382SourceAll
import QiushiGlobalOrbitUnused382DeadSourceAll
import QiushiGlobalOrbitUnused382IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane382UnusedGenBool : PlaneExtBool plane382UnusedGenConfig where
  hSectionCoset := plane382UnusedGenSectionAll
  hDeadCover := plane382UnusedGenDeadAll
  hPlaneLeSource := plane382UnusedGenSourceAll
  hPlaneLeDead := plane382UnusedGenDeadSourceAll
  hIndicator := plane382UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
