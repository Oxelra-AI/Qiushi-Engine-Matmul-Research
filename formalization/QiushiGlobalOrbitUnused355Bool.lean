import QiushiGlobalOrbitUnused355SectionAll
import QiushiGlobalOrbitUnused355DeadAll
import QiushiGlobalOrbitUnused355SourceAll
import QiushiGlobalOrbitUnused355DeadSourceAll
import QiushiGlobalOrbitUnused355IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane355UnusedGenBool : PlaneExtBool plane355UnusedGenConfig where
  hSectionCoset := plane355UnusedGenSectionAll
  hDeadCover := plane355UnusedGenDeadAll
  hPlaneLeSource := plane355UnusedGenSourceAll
  hPlaneLeDead := plane355UnusedGenDeadSourceAll
  hIndicator := plane355UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
