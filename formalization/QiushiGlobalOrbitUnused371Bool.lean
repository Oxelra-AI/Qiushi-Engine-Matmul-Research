import QiushiGlobalOrbitUnused371SectionAll
import QiushiGlobalOrbitUnused371DeadAll
import QiushiGlobalOrbitUnused371SourceAll
import QiushiGlobalOrbitUnused371DeadSourceAll
import QiushiGlobalOrbitUnused371IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane371UnusedGenBool : PlaneExtBool plane371UnusedGenConfig where
  hSectionCoset := plane371UnusedGenSectionAll
  hDeadCover := plane371UnusedGenDeadAll
  hPlaneLeSource := plane371UnusedGenSourceAll
  hPlaneLeDead := plane371UnusedGenDeadSourceAll
  hIndicator := plane371UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
