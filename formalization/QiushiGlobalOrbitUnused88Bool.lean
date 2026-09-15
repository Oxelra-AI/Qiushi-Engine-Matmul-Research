import QiushiGlobalOrbitUnused88SectionAll
import QiushiGlobalOrbitUnused88DeadAll
import QiushiGlobalOrbitUnused88SourceAll
import QiushiGlobalOrbitUnused88DeadSourceAll
import QiushiGlobalOrbitUnused88IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane88UnusedGenBool : PlaneExtBool plane88UnusedGenConfig where
  hSectionCoset := plane88UnusedGenSectionAll
  hDeadCover := plane88UnusedGenDeadAll
  hPlaneLeSource := plane88UnusedGenSourceAll
  hPlaneLeDead := plane88UnusedGenDeadSourceAll
  hIndicator := plane88UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
