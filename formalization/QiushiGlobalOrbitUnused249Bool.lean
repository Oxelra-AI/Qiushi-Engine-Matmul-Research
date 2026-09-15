import QiushiGlobalOrbitUnused249SectionAll
import QiushiGlobalOrbitUnused249DeadAll
import QiushiGlobalOrbitUnused249SourceAll
import QiushiGlobalOrbitUnused249DeadSourceAll
import QiushiGlobalOrbitUnused249IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane249UnusedGenBool : PlaneExtBool plane249UnusedGenConfig where
  hSectionCoset := plane249UnusedGenSectionAll
  hDeadCover := plane249UnusedGenDeadAll
  hPlaneLeSource := plane249UnusedGenSourceAll
  hPlaneLeDead := plane249UnusedGenDeadSourceAll
  hIndicator := plane249UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
