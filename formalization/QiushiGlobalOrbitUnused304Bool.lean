import QiushiGlobalOrbitUnused304SectionAll
import QiushiGlobalOrbitUnused304DeadAll
import QiushiGlobalOrbitUnused304SourceAll
import QiushiGlobalOrbitUnused304DeadSourceAll
import QiushiGlobalOrbitUnused304IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane304UnusedGenBool : PlaneExtBool plane304UnusedGenConfig where
  hSectionCoset := plane304UnusedGenSectionAll
  hDeadCover := plane304UnusedGenDeadAll
  hPlaneLeSource := plane304UnusedGenSourceAll
  hPlaneLeDead := plane304UnusedGenDeadSourceAll
  hIndicator := plane304UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
