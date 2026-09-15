import QiushiGlobalOrbitUnused307SectionAll
import QiushiGlobalOrbitUnused307DeadAll
import QiushiGlobalOrbitUnused307SourceAll
import QiushiGlobalOrbitUnused307DeadSourceAll
import QiushiGlobalOrbitUnused307IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane307UnusedGenBool : PlaneExtBool plane307UnusedGenConfig where
  hSectionCoset := plane307UnusedGenSectionAll
  hDeadCover := plane307UnusedGenDeadAll
  hPlaneLeSource := plane307UnusedGenSourceAll
  hPlaneLeDead := plane307UnusedGenDeadSourceAll
  hIndicator := plane307UnusedGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
