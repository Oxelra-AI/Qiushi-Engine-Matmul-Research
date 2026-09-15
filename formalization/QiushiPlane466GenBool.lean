import QiushiPlane466GenSectionAll
import QiushiPlane466GenDeadAll
import QiushiPlane466GenSourceAll
import QiushiPlane466GenDeadSourceAll
import QiushiPlane466GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane466GenBool : PlaneExtBool plane466GenConfig where
  hSectionCoset := plane466GenSectionAll
  hDeadCover := plane466GenDeadAll
  hPlaneLeSource := plane466GenSourceAll
  hPlaneLeDead := plane466GenDeadSourceAll
  hIndicator := plane466GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
