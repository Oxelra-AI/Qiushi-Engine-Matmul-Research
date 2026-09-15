import QiushiPlane491GenSectionAll
import QiushiPlane491GenDeadAll
import QiushiPlane491GenSourceAll
import QiushiPlane491GenDeadSourceAll
import QiushiPlane491GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane491GenBool : PlaneExtBool plane491GenConfig where
  hSectionCoset := plane491GenSectionAll
  hDeadCover := plane491GenDeadAll
  hPlaneLeSource := plane491GenSourceAll
  hPlaneLeDead := plane491GenDeadSourceAll
  hIndicator := plane491GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
