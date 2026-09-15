import QiushiGlobalOrbitUnused301SectionAll
import QiushiGlobalOrbitUnused301DeadAll
import QiushiGlobalOrbitUnused301SourceAll
import QiushiGlobalOrbitUnused301DeadSourceAll
import QiushiGlobalOrbitUnused301IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane301UnusedGenBool : PlaneExtBool plane301UnusedGenConfig where
  hSectionCoset := plane301UnusedGenSectionAll
  hDeadCover := plane301UnusedGenDeadAll
  hPlaneLeSource := plane301UnusedGenSourceAll
  hPlaneLeDead := plane301UnusedGenDeadSourceAll
  hIndicator := plane301UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
