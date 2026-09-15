import QiushiPlane254GenSectionAll
import QiushiPlane254GenDeadAll
import QiushiPlane254GenSourceAll
import QiushiPlane254GenDeadSourceAll
import QiushiPlane254GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane254GenBool : PlaneExtBool plane254GenConfig where
  hSectionCoset := plane254GenSectionAll
  hDeadCover := plane254GenDeadAll
  hPlaneLeSource := plane254GenSourceAll
  hPlaneLeDead := plane254GenDeadSourceAll
  hIndicator := plane254GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
