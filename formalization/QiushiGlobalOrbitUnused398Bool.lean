import QiushiGlobalOrbitUnused398SectionAll
import QiushiGlobalOrbitUnused398DeadAll
import QiushiGlobalOrbitUnused398SourceAll
import QiushiGlobalOrbitUnused398DeadSourceAll
import QiushiGlobalOrbitUnused398IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane398UnusedGenBool : PlaneExtBool plane398UnusedGenConfig where
  hSectionCoset := plane398UnusedGenSectionAll
  hDeadCover := plane398UnusedGenDeadAll
  hPlaneLeSource := plane398UnusedGenSourceAll
  hPlaneLeDead := plane398UnusedGenDeadSourceAll
  hIndicator := plane398UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
