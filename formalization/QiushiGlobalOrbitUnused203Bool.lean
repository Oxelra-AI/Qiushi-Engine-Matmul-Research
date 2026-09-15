import QiushiGlobalOrbitUnused203SectionAll
import QiushiGlobalOrbitUnused203DeadAll
import QiushiGlobalOrbitUnused203SourceAll
import QiushiGlobalOrbitUnused203DeadSourceAll
import QiushiGlobalOrbitUnused203IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane203UnusedGenBool : PlaneExtBool plane203UnusedGenConfig where
  hSectionCoset := plane203UnusedGenSectionAll
  hDeadCover := plane203UnusedGenDeadAll
  hPlaneLeSource := plane203UnusedGenSourceAll
  hPlaneLeDead := plane203UnusedGenDeadSourceAll
  hIndicator := plane203UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
