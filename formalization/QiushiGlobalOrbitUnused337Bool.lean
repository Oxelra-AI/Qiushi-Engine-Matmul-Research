import QiushiGlobalOrbitUnused337SectionAll
import QiushiGlobalOrbitUnused337DeadAll
import QiushiGlobalOrbitUnused337SourceAll
import QiushiGlobalOrbitUnused337DeadSourceAll
import QiushiGlobalOrbitUnused337IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane337UnusedGenBool : PlaneExtBool plane337UnusedGenConfig where
  hSectionCoset := plane337UnusedGenSectionAll
  hDeadCover := plane337UnusedGenDeadAll
  hPlaneLeSource := plane337UnusedGenSourceAll
  hPlaneLeDead := plane337UnusedGenDeadSourceAll
  hIndicator := plane337UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
