import QiushiGlobalOrbitUnused394SectionAll
import QiushiGlobalOrbitUnused394DeadAll
import QiushiGlobalOrbitUnused394SourceAll
import QiushiGlobalOrbitUnused394DeadSourceAll
import QiushiGlobalOrbitUnused394IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane394UnusedGenBool : PlaneExtBool plane394UnusedGenConfig where
  hSectionCoset := plane394UnusedGenSectionAll
  hDeadCover := plane394UnusedGenDeadAll
  hPlaneLeSource := plane394UnusedGenSourceAll
  hPlaneLeDead := plane394UnusedGenDeadSourceAll
  hIndicator := plane394UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
