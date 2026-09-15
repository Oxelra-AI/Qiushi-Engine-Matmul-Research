import QiushiGlobalOrbitUnused306SectionAll
import QiushiGlobalOrbitUnused306DeadAll
import QiushiGlobalOrbitUnused306SourceAll
import QiushiGlobalOrbitUnused306DeadSourceAll
import QiushiGlobalOrbitUnused306IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane306UnusedGenBool : PlaneExtBool plane306UnusedGenConfig where
  hSectionCoset := plane306UnusedGenSectionAll
  hDeadCover := plane306UnusedGenDeadAll
  hPlaneLeSource := plane306UnusedGenSourceAll
  hPlaneLeDead := plane306UnusedGenDeadSourceAll
  hIndicator := plane306UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
