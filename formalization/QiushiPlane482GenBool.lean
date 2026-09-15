import QiushiPlane482GenSectionAll
import QiushiPlane482GenDeadAll
import QiushiPlane482GenSourceAll
import QiushiPlane482GenDeadSourceAll
import QiushiPlane482GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane482GenBool : PlaneExtBool plane482GenConfig where
  hSectionCoset := plane482GenSectionAll
  hDeadCover := plane482GenDeadAll
  hPlaneLeSource := plane482GenSourceAll
  hPlaneLeDead := plane482GenDeadSourceAll
  hIndicator := plane482GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
