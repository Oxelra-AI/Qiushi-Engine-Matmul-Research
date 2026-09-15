import QiushiPlane419GenSectionAll
import QiushiPlane419GenDeadAll
import QiushiPlane419GenSourceAll
import QiushiPlane419GenDeadSourceAll
import QiushiPlane419GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane419GenBool : PlaneExtBool plane419GenConfig where
  hSectionCoset := plane419GenSectionAll
  hDeadCover := plane419GenDeadAll
  hPlaneLeSource := plane419GenSourceAll
  hPlaneLeDead := plane419GenDeadSourceAll
  hIndicator := plane419GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
