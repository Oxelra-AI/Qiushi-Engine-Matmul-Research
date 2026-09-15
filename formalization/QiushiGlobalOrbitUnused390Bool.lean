import QiushiGlobalOrbitUnused390SectionAll
import QiushiGlobalOrbitUnused390DeadAll
import QiushiGlobalOrbitUnused390SourceAll
import QiushiGlobalOrbitUnused390DeadSourceAll
import QiushiGlobalOrbitUnused390IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane390UnusedGenBool : PlaneExtBool plane390UnusedGenConfig where
  hSectionCoset := plane390UnusedGenSectionAll
  hDeadCover := plane390UnusedGenDeadAll
  hPlaneLeSource := plane390UnusedGenSourceAll
  hPlaneLeDead := plane390UnusedGenDeadSourceAll
  hIndicator := plane390UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
