import QiushiPlane472GenSectionAll
import QiushiPlane472GenDeadAll
import QiushiPlane472GenSourceAll
import QiushiPlane472GenDeadSourceAll
import QiushiPlane472GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane472GenBool : PlaneExtBool plane472GenConfig where
  hSectionCoset := plane472GenSectionAll
  hDeadCover := plane472GenDeadAll
  hPlaneLeSource := plane472GenSourceAll
  hPlaneLeDead := plane472GenDeadSourceAll
  hIndicator := plane472GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
