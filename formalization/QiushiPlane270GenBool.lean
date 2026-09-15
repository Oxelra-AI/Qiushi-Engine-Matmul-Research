import QiushiPlane270GenSectionAll
import QiushiPlane270GenDeadAll
import QiushiPlane270GenSourceAll
import QiushiPlane270GenDeadSourceAll
import QiushiPlane270GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane270GenBool : PlaneExtBool plane270GenConfig where
  hSectionCoset := plane270GenSectionAll
  hDeadCover := plane270GenDeadAll
  hPlaneLeSource := plane270GenSourceAll
  hPlaneLeDead := plane270GenDeadSourceAll
  hIndicator := plane270GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
