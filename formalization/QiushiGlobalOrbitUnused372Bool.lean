import QiushiGlobalOrbitUnused372SectionAll
import QiushiGlobalOrbitUnused372DeadAll
import QiushiGlobalOrbitUnused372SourceAll
import QiushiGlobalOrbitUnused372DeadSourceAll
import QiushiGlobalOrbitUnused372IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane372UnusedGenBool : PlaneExtBool plane372UnusedGenConfig where
  hSectionCoset := plane372UnusedGenSectionAll
  hDeadCover := plane372UnusedGenDeadAll
  hPlaneLeSource := plane372UnusedGenSourceAll
  hPlaneLeDead := plane372UnusedGenDeadSourceAll
  hIndicator := plane372UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
