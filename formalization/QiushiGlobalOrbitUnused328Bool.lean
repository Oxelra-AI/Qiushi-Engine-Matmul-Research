import QiushiGlobalOrbitUnused328SectionAll
import QiushiGlobalOrbitUnused328DeadAll
import QiushiGlobalOrbitUnused328SourceAll
import QiushiGlobalOrbitUnused328DeadSourceAll
import QiushiGlobalOrbitUnused328IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane328UnusedGenBool : PlaneExtBool plane328UnusedGenConfig where
  hSectionCoset := plane328UnusedGenSectionAll
  hDeadCover := plane328UnusedGenDeadAll
  hPlaneLeSource := plane328UnusedGenSourceAll
  hPlaneLeDead := plane328UnusedGenDeadSourceAll
  hIndicator := plane328UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
