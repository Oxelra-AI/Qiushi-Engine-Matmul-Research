import QiushiGlobalOrbitUnused403SectionAll
import QiushiGlobalOrbitUnused403DeadAll
import QiushiGlobalOrbitUnused403SourceAll
import QiushiGlobalOrbitUnused403DeadSourceAll
import QiushiGlobalOrbitUnused403IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane403UnusedGenBool : PlaneExtBool plane403UnusedGenConfig where
  hSectionCoset := plane403UnusedGenSectionAll
  hDeadCover := plane403UnusedGenDeadAll
  hPlaneLeSource := plane403UnusedGenSourceAll
  hPlaneLeDead := plane403UnusedGenDeadSourceAll
  hIndicator := plane403UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
