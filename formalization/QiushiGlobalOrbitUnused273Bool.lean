import QiushiGlobalOrbitUnused273SectionAll
import QiushiGlobalOrbitUnused273DeadAll
import QiushiGlobalOrbitUnused273SourceAll
import QiushiGlobalOrbitUnused273DeadSourceAll
import QiushiGlobalOrbitUnused273IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane273UnusedGenBool : PlaneExtBool plane273UnusedGenConfig where
  hSectionCoset := plane273UnusedGenSectionAll
  hDeadCover := plane273UnusedGenDeadAll
  hPlaneLeSource := plane273UnusedGenSourceAll
  hPlaneLeDead := plane273UnusedGenDeadSourceAll
  hIndicator := plane273UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
