import QiushiGlobalOrbitUnused309SectionAll
import QiushiGlobalOrbitUnused309DeadAll
import QiushiGlobalOrbitUnused309SourceAll
import QiushiGlobalOrbitUnused309DeadSourceAll
import QiushiGlobalOrbitUnused309IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane309UnusedGenBool : PlaneExtBool plane309UnusedGenConfig where
  hSectionCoset := plane309UnusedGenSectionAll
  hDeadCover := plane309UnusedGenDeadAll
  hPlaneLeSource := plane309UnusedGenSourceAll
  hPlaneLeDead := plane309UnusedGenDeadSourceAll
  hIndicator := plane309UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
