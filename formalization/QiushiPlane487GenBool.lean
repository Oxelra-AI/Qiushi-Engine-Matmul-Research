import QiushiPlane487GenSectionAll
import QiushiPlane487GenDeadAll
import QiushiPlane487GenSourceAll
import QiushiPlane487GenDeadSourceAll
import QiushiPlane487GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane487GenBool : PlaneExtBool plane487GenConfig where
  hSectionCoset := plane487GenSectionAll
  hDeadCover := plane487GenDeadAll
  hPlaneLeSource := plane487GenSourceAll
  hPlaneLeDead := plane487GenDeadSourceAll
  hIndicator := plane487GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
