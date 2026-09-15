import QiushiGlobalOrbitUnused321SectionAll
import QiushiGlobalOrbitUnused321DeadAll
import QiushiGlobalOrbitUnused321SourceAll
import QiushiGlobalOrbitUnused321DeadSourceAll
import QiushiGlobalOrbitUnused321IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane321UnusedGenBool : PlaneExtBool plane321UnusedGenConfig where
  hSectionCoset := plane321UnusedGenSectionAll
  hDeadCover := plane321UnusedGenDeadAll
  hPlaneLeSource := plane321UnusedGenSourceAll
  hPlaneLeDead := plane321UnusedGenDeadSourceAll
  hIndicator := plane321UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
