import QiushiPlane471GenSectionAll
import QiushiPlane471GenDeadAll
import QiushiPlane471GenSourceAll
import QiushiPlane471GenDeadSourceAll
import QiushiPlane471GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane471GenBool : PlaneExtBool plane471GenConfig where
  hSectionCoset := plane471GenSectionAll
  hDeadCover := plane471GenDeadAll
  hPlaneLeSource := plane471GenSourceAll
  hPlaneLeDead := plane471GenDeadSourceAll
  hIndicator := plane471GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
