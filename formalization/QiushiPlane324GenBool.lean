import QiushiPlane324GenSectionAll
import QiushiPlane324GenDeadAll
import QiushiPlane324GenSourceAll
import QiushiPlane324GenDeadSourceAll
import QiushiPlane324GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane324GenBool : PlaneExtBool plane324GenConfig where
  hSectionCoset := plane324GenSectionAll
  hDeadCover := plane324GenDeadAll
  hPlaneLeSource := plane324GenSourceAll
  hPlaneLeDead := plane324GenDeadSourceAll
  hIndicator := plane324GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
