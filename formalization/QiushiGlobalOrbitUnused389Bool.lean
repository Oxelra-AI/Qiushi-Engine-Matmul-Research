import QiushiGlobalOrbitUnused389SectionAll
import QiushiGlobalOrbitUnused389DeadAll
import QiushiGlobalOrbitUnused389SourceAll
import QiushiGlobalOrbitUnused389DeadSourceAll
import QiushiGlobalOrbitUnused389IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane389UnusedGenBool : PlaneExtBool plane389UnusedGenConfig where
  hSectionCoset := plane389UnusedGenSectionAll
  hDeadCover := plane389UnusedGenDeadAll
  hPlaneLeSource := plane389UnusedGenSourceAll
  hPlaneLeDead := plane389UnusedGenDeadSourceAll
  hIndicator := plane389UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
