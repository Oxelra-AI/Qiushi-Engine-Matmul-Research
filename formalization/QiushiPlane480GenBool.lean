import QiushiPlane480GenSectionAll
import QiushiPlane480GenDeadAll
import QiushiPlane480GenSourceAll
import QiushiPlane480GenDeadSourceAll
import QiushiPlane480GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane480GenBool : PlaneExtBool plane480GenConfig where
  hSectionCoset := plane480GenSectionAll
  hDeadCover := plane480GenDeadAll
  hPlaneLeSource := plane480GenSourceAll
  hPlaneLeDead := plane480GenDeadSourceAll
  hIndicator := plane480GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
