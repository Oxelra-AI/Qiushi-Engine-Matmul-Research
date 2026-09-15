import QiushiPlane433GenSectionAll
import QiushiPlane433GenDeadAll
import QiushiPlane433GenSourceAll
import QiushiPlane433GenDeadSourceAll
import QiushiPlane433GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane433GenBool : PlaneExtBool plane433GenConfig where
  hSectionCoset := plane433GenSectionAll
  hDeadCover := plane433GenDeadAll
  hPlaneLeSource := plane433GenSourceAll
  hPlaneLeDead := plane433GenDeadSourceAll
  hIndicator := plane433GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
