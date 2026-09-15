import QiushiGlobalOrbitUnused333SectionAll
import QiushiGlobalOrbitUnused333DeadAll
import QiushiGlobalOrbitUnused333SourceAll
import QiushiGlobalOrbitUnused333DeadSourceAll
import QiushiGlobalOrbitUnused333IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane333UnusedGenBool : PlaneExtBool plane333UnusedGenConfig where
  hSectionCoset := plane333UnusedGenSectionAll
  hDeadCover := plane333UnusedGenDeadAll
  hPlaneLeSource := plane333UnusedGenSourceAll
  hPlaneLeDead := plane333UnusedGenDeadSourceAll
  hIndicator := plane333UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
