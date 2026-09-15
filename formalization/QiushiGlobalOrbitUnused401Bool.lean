import QiushiGlobalOrbitUnused401SectionAll
import QiushiGlobalOrbitUnused401DeadAll
import QiushiGlobalOrbitUnused401SourceAll
import QiushiGlobalOrbitUnused401DeadSourceAll
import QiushiGlobalOrbitUnused401IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane401UnusedGenBool : PlaneExtBool plane401UnusedGenConfig where
  hSectionCoset := plane401UnusedGenSectionAll
  hDeadCover := plane401UnusedGenDeadAll
  hPlaneLeSource := plane401UnusedGenSourceAll
  hPlaneLeDead := plane401UnusedGenDeadSourceAll
  hIndicator := plane401UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
