import QiushiPlane486GenSectionAll
import QiushiPlane486GenDeadAll
import QiushiPlane486GenSourceAll
import QiushiPlane486GenDeadSourceAll
import QiushiPlane486GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane486GenBool : PlaneExtBool plane486GenConfig where
  hSectionCoset := plane486GenSectionAll
  hDeadCover := plane486GenDeadAll
  hPlaneLeSource := plane486GenSourceAll
  hPlaneLeDead := plane486GenDeadSourceAll
  hIndicator := plane486GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
