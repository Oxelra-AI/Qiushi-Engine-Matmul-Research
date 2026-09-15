import QiushiGlobalOrbitUnused339SectionAll
import QiushiGlobalOrbitUnused339DeadAll
import QiushiGlobalOrbitUnused339SourceAll
import QiushiGlobalOrbitUnused339DeadSourceAll
import QiushiGlobalOrbitUnused339IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane339UnusedGenBool : PlaneExtBool plane339UnusedGenConfig where
  hSectionCoset := plane339UnusedGenSectionAll
  hDeadCover := plane339UnusedGenDeadAll
  hPlaneLeSource := plane339UnusedGenSourceAll
  hPlaneLeDead := plane339UnusedGenDeadSourceAll
  hIndicator := plane339UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
