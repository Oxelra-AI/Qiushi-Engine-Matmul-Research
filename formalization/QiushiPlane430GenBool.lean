import QiushiPlane430GenSectionAll
import QiushiPlane430GenDeadAll
import QiushiPlane430GenSourceAll
import QiushiPlane430GenDeadSourceAll
import QiushiPlane430GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane430GenBool : PlaneExtBool plane430GenConfig where
  hSectionCoset := plane430GenSectionAll
  hDeadCover := plane430GenDeadAll
  hPlaneLeSource := plane430GenSourceAll
  hPlaneLeDead := plane430GenDeadSourceAll
  hIndicator := plane430GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
