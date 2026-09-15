import QiushiPlane267GenSectionAll
import QiushiPlane267GenDeadAll
import QiushiPlane267GenSourceAll
import QiushiPlane267GenDeadSourceAll
import QiushiPlane267GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane267GenBool : PlaneExtBool plane267GenConfig where
  hSectionCoset := plane267GenSectionAll
  hDeadCover := plane267GenDeadAll
  hPlaneLeSource := plane267GenSourceAll
  hPlaneLeDead := plane267GenDeadSourceAll
  hIndicator := plane267GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
