import QiushiGlobalOrbitUnused312SectionAll
import QiushiGlobalOrbitUnused312DeadAll
import QiushiGlobalOrbitUnused312SourceAll
import QiushiGlobalOrbitUnused312DeadSourceAll
import QiushiGlobalOrbitUnused312IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane312UnusedGenBool : PlaneExtBool plane312UnusedGenConfig where
  hSectionCoset := plane312UnusedGenSectionAll
  hDeadCover := plane312UnusedGenDeadAll
  hPlaneLeSource := plane312UnusedGenSourceAll
  hPlaneLeDead := plane312UnusedGenDeadSourceAll
  hIndicator := plane312UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
