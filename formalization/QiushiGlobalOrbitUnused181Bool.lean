import QiushiGlobalOrbitUnused181SectionAll
import QiushiGlobalOrbitUnused181DeadAll
import QiushiGlobalOrbitUnused181SourceAll
import QiushiGlobalOrbitUnused181DeadSourceAll
import QiushiGlobalOrbitUnused181IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane181UnusedGenBool : PlaneExtBool plane181UnusedGenConfig where
  hSectionCoset := plane181UnusedGenSectionAll
  hDeadCover := plane181UnusedGenDeadAll
  hPlaneLeSource := plane181UnusedGenSourceAll
  hPlaneLeDead := plane181UnusedGenDeadSourceAll
  hIndicator := plane181UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
