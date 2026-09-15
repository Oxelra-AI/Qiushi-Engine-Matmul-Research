import QiushiPlane338GenSectionAll
import QiushiPlane338GenDeadAll
import QiushiPlane338GenSourceAll
import QiushiPlane338GenDeadSourceAll
import QiushiPlane338GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane338GenBool : PlaneExtBool plane338GenConfig where
  hSectionCoset := plane338GenSectionAll
  hDeadCover := plane338GenDeadAll
  hPlaneLeSource := plane338GenSourceAll
  hPlaneLeDead := plane338GenDeadSourceAll
  hIndicator := plane338GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
