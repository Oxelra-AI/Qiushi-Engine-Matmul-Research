import QiushiGlobalOrbitUnused284SectionAll
import QiushiGlobalOrbitUnused284DeadAll
import QiushiGlobalOrbitUnused284SourceAll
import QiushiGlobalOrbitUnused284DeadSourceAll
import QiushiGlobalOrbitUnused284IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane284UnusedGenBool : PlaneExtBool plane284UnusedGenConfig where
  hSectionCoset := plane284UnusedGenSectionAll
  hDeadCover := plane284UnusedGenDeadAll
  hPlaneLeSource := plane284UnusedGenSourceAll
  hPlaneLeDead := plane284UnusedGenDeadSourceAll
  hIndicator := plane284UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
