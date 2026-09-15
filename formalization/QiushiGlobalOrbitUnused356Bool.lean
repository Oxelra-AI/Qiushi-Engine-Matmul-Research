import QiushiGlobalOrbitUnused356SectionAll
import QiushiGlobalOrbitUnused356DeadAll
import QiushiGlobalOrbitUnused356SourceAll
import QiushiGlobalOrbitUnused356DeadSourceAll
import QiushiGlobalOrbitUnused356IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane356UnusedGenBool : PlaneExtBool plane356UnusedGenConfig where
  hSectionCoset := plane356UnusedGenSectionAll
  hDeadCover := plane356UnusedGenDeadAll
  hPlaneLeSource := plane356UnusedGenSourceAll
  hPlaneLeDead := plane356UnusedGenDeadSourceAll
  hIndicator := plane356UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
