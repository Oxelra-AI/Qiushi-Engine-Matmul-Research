import QiushiGlobalOrbitUnused302SectionAll
import QiushiGlobalOrbitUnused302DeadAll
import QiushiGlobalOrbitUnused302SourceAll
import QiushiGlobalOrbitUnused302DeadSourceAll
import QiushiGlobalOrbitUnused302IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane302UnusedGenBool : PlaneExtBool plane302UnusedGenConfig where
  hSectionCoset := plane302UnusedGenSectionAll
  hDeadCover := plane302UnusedGenDeadAll
  hPlaneLeSource := plane302UnusedGenSourceAll
  hPlaneLeDead := plane302UnusedGenDeadSourceAll
  hIndicator := plane302UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
