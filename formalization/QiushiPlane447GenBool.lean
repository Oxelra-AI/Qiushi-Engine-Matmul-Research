import QiushiPlane447GenSectionAll
import QiushiPlane447GenDeadAll
import QiushiPlane447GenSourceAll
import QiushiPlane447GenDeadSourceAll
import QiushiPlane447GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane447GenBool : PlaneExtBool plane447GenConfig where
  hSectionCoset := plane447GenSectionAll
  hDeadCover := plane447GenDeadAll
  hPlaneLeSource := plane447GenSourceAll
  hPlaneLeDead := plane447GenDeadSourceAll
  hIndicator := plane447GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
