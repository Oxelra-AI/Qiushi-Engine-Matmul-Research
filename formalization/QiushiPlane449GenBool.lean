import QiushiPlane449GenSectionAll
import QiushiPlane449GenDeadAll
import QiushiPlane449GenSourceAll
import QiushiPlane449GenDeadSourceAll
import QiushiPlane449GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane449GenBool : PlaneExtBool plane449GenConfig where
  hSectionCoset := plane449GenSectionAll
  hDeadCover := plane449GenDeadAll
  hPlaneLeSource := plane449GenSourceAll
  hPlaneLeDead := plane449GenDeadSourceAll
  hIndicator := plane449GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
