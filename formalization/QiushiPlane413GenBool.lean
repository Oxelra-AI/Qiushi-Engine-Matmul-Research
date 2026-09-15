import QiushiPlane413GenSectionAll
import QiushiPlane413GenDeadAll
import QiushiPlane413GenSourceAll
import QiushiPlane413GenDeadSourceAll
import QiushiPlane413GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane413GenBool : PlaneExtBool plane413GenConfig where
  hSectionCoset := plane413GenSectionAll
  hDeadCover := plane413GenDeadAll
  hPlaneLeSource := plane413GenSourceAll
  hPlaneLeDead := plane413GenDeadSourceAll
  hIndicator := plane413GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
