import QiushiGlobalOrbitUnused408SectionAll
import QiushiGlobalOrbitUnused408DeadAll
import QiushiGlobalOrbitUnused408SourceAll
import QiushiGlobalOrbitUnused408DeadSourceAll
import QiushiGlobalOrbitUnused408IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane408UnusedGenBool : PlaneExtBool plane408UnusedGenConfig where
  hSectionCoset := plane408UnusedGenSectionAll
  hDeadCover := plane408UnusedGenDeadAll
  hPlaneLeSource := plane408UnusedGenSourceAll
  hPlaneLeDead := plane408UnusedGenDeadSourceAll
  hIndicator := plane408UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
