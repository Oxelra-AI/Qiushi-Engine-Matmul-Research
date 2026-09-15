import QiushiPlane457GenSectionAll
import QiushiPlane457GenDeadAll
import QiushiPlane457GenSourceAll
import QiushiPlane457GenDeadSourceAll
import QiushiPlane457GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane457GenBool : PlaneExtBool plane457GenConfig where
  hSectionCoset := plane457GenSectionAll
  hDeadCover := plane457GenDeadAll
  hPlaneLeSource := plane457GenSourceAll
  hPlaneLeDead := plane457GenDeadSourceAll
  hIndicator := plane457GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
