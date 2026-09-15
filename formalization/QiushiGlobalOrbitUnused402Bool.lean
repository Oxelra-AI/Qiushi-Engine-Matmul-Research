import QiushiGlobalOrbitUnused402SectionAll
import QiushiGlobalOrbitUnused402DeadAll
import QiushiGlobalOrbitUnused402SourceAll
import QiushiGlobalOrbitUnused402DeadSourceAll
import QiushiGlobalOrbitUnused402IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane402UnusedGenBool : PlaneExtBool plane402UnusedGenConfig where
  hSectionCoset := plane402UnusedGenSectionAll
  hDeadCover := plane402UnusedGenDeadAll
  hPlaneLeSource := plane402UnusedGenSourceAll
  hPlaneLeDead := plane402UnusedGenDeadSourceAll
  hIndicator := plane402UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
