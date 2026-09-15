import QiushiPlane467GenSectionAll
import QiushiPlane467GenDeadAll
import QiushiPlane467GenSourceAll
import QiushiPlane467GenDeadSourceAll
import QiushiPlane467GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane467GenBool : PlaneExtBool plane467GenConfig where
  hSectionCoset := plane467GenSectionAll
  hDeadCover := plane467GenDeadAll
  hPlaneLeSource := plane467GenSourceAll
  hPlaneLeDead := plane467GenDeadSourceAll
  hIndicator := plane467GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
