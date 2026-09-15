import QiushiGlobalOrbitUnused387SectionAll
import QiushiGlobalOrbitUnused387DeadAll
import QiushiGlobalOrbitUnused387SourceAll
import QiushiGlobalOrbitUnused387DeadSourceAll
import QiushiGlobalOrbitUnused387IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane387UnusedGenBool : PlaneExtBool plane387UnusedGenConfig where
  hSectionCoset := plane387UnusedGenSectionAll
  hDeadCover := plane387UnusedGenDeadAll
  hPlaneLeSource := plane387UnusedGenSourceAll
  hPlaneLeDead := plane387UnusedGenDeadSourceAll
  hIndicator := plane387UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
