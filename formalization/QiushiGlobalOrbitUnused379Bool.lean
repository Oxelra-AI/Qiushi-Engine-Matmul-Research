import QiushiGlobalOrbitUnused379SectionAll
import QiushiGlobalOrbitUnused379DeadAll
import QiushiGlobalOrbitUnused379SourceAll
import QiushiGlobalOrbitUnused379DeadSourceAll
import QiushiGlobalOrbitUnused379IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane379UnusedGenBool : PlaneExtBool plane379UnusedGenConfig where
  hSectionCoset := plane379UnusedGenSectionAll
  hDeadCover := plane379UnusedGenDeadAll
  hPlaneLeSource := plane379UnusedGenSourceAll
  hPlaneLeDead := plane379UnusedGenDeadSourceAll
  hIndicator := plane379UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
