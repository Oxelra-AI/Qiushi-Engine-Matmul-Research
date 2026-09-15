import QiushiPlane315GenSectionAll
import QiushiPlane315GenDeadAll
import QiushiPlane315GenSourceAll
import QiushiPlane315GenDeadSourceAll
import QiushiPlane315GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane315GenBool : PlaneExtBool plane315GenConfig where
  hSectionCoset := plane315GenSectionAll
  hDeadCover := plane315GenDeadAll
  hPlaneLeSource := plane315GenSourceAll
  hPlaneLeDead := plane315GenDeadSourceAll
  hIndicator := plane315GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
