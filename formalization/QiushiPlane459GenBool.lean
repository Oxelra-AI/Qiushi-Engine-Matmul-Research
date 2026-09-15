import QiushiPlane459GenSectionAll
import QiushiPlane459GenDeadAll
import QiushiPlane459GenSourceAll
import QiushiPlane459GenDeadSourceAll
import QiushiPlane459GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane459GenBool : PlaneExtBool plane459GenConfig where
  hSectionCoset := plane459GenSectionAll
  hDeadCover := plane459GenDeadAll
  hPlaneLeSource := plane459GenSourceAll
  hPlaneLeDead := plane459GenDeadSourceAll
  hIndicator := plane459GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
