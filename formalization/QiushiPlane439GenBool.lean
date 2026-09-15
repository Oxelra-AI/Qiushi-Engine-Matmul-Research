import QiushiPlane439GenSectionAll
import QiushiPlane439GenDeadAll
import QiushiPlane439GenSourceAll
import QiushiPlane439GenDeadSourceAll
import QiushiPlane439GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane439GenBool : PlaneExtBool plane439GenConfig where
  hSectionCoset := plane439GenSectionAll
  hDeadCover := plane439GenDeadAll
  hPlaneLeSource := plane439GenSourceAll
  hPlaneLeDead := plane439GenDeadSourceAll
  hIndicator := plane439GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
