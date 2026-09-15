import QiushiGlobalOrbitUnused399SectionAll
import QiushiGlobalOrbitUnused399DeadAll
import QiushiGlobalOrbitUnused399SourceAll
import QiushiGlobalOrbitUnused399DeadSourceAll
import QiushiGlobalOrbitUnused399IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane399UnusedGenBool : PlaneExtBool plane399UnusedGenConfig where
  hSectionCoset := plane399UnusedGenSectionAll
  hDeadCover := plane399UnusedGenDeadAll
  hPlaneLeSource := plane399UnusedGenSourceAll
  hPlaneLeDead := plane399UnusedGenDeadSourceAll
  hIndicator := plane399UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
