import QiushiGlobalOrbitUnused378SectionAll
import QiushiGlobalOrbitUnused378DeadAll
import QiushiGlobalOrbitUnused378SourceAll
import QiushiGlobalOrbitUnused378DeadSourceAll
import QiushiGlobalOrbitUnused378IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane378UnusedGenBool : PlaneExtBool plane378UnusedGenConfig where
  hSectionCoset := plane378UnusedGenSectionAll
  hDeadCover := plane378UnusedGenDeadAll
  hPlaneLeSource := plane378UnusedGenSourceAll
  hPlaneLeDead := plane378UnusedGenDeadSourceAll
  hIndicator := plane378UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
