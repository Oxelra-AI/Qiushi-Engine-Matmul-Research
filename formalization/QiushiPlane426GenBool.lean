import QiushiPlane426GenSectionAll
import QiushiPlane426GenDeadAll
import QiushiPlane426GenSourceAll
import QiushiPlane426GenDeadSourceAll
import QiushiPlane426GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane426GenBool : PlaneExtBool plane426GenConfig where
  hSectionCoset := plane426GenSectionAll
  hDeadCover := plane426GenDeadAll
  hPlaneLeSource := plane426GenSourceAll
  hPlaneLeDead := plane426GenDeadSourceAll
  hIndicator := plane426GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
