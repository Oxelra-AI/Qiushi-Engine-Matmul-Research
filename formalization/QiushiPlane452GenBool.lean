import QiushiPlane452GenSectionAll
import QiushiPlane452GenDeadAll
import QiushiPlane452GenSourceAll
import QiushiPlane452GenDeadSourceAll
import QiushiPlane452GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane452GenBool : PlaneExtBool plane452GenConfig where
  hSectionCoset := plane452GenSectionAll
  hDeadCover := plane452GenDeadAll
  hPlaneLeSource := plane452GenSourceAll
  hPlaneLeDead := plane452GenDeadSourceAll
  hIndicator := plane452GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
