import QiushiPlane468GenSectionAll
import QiushiPlane468GenDeadAll
import QiushiPlane468GenSourceAll
import QiushiPlane468GenDeadSourceAll
import QiushiPlane468GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane468GenBool : PlaneExtBool plane468GenConfig where
  hSectionCoset := plane468GenSectionAll
  hDeadCover := plane468GenDeadAll
  hPlaneLeSource := plane468GenSourceAll
  hPlaneLeDead := plane468GenDeadSourceAll
  hIndicator := plane468GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
