import QiushiGlobalOrbitUnused392SectionAll
import QiushiGlobalOrbitUnused392DeadAll
import QiushiGlobalOrbitUnused392SourceAll
import QiushiGlobalOrbitUnused392DeadSourceAll
import QiushiGlobalOrbitUnused392IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane392UnusedGenBool : PlaneExtBool plane392UnusedGenConfig where
  hSectionCoset := plane392UnusedGenSectionAll
  hDeadCover := plane392UnusedGenDeadAll
  hPlaneLeSource := plane392UnusedGenSourceAll
  hPlaneLeDead := plane392UnusedGenDeadSourceAll
  hIndicator := plane392UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
