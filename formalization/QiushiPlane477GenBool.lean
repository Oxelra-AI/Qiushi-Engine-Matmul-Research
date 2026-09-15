import QiushiPlane477GenSectionAll
import QiushiPlane477GenDeadAll
import QiushiPlane477GenSourceAll
import QiushiPlane477GenDeadSourceAll
import QiushiPlane477GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane477GenBool : PlaneExtBool plane477GenConfig where
  hSectionCoset := plane477GenSectionAll
  hDeadCover := plane477GenDeadAll
  hPlaneLeSource := plane477GenSourceAll
  hPlaneLeDead := plane477GenDeadSourceAll
  hIndicator := plane477GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
