import QiushiPlane461GenSectionAll
import QiushiPlane461GenDeadAll
import QiushiPlane461GenSourceAll
import QiushiPlane461GenDeadSourceAll
import QiushiPlane461GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane461GenBool : PlaneExtBool plane461GenConfig where
  hSectionCoset := plane461GenSectionAll
  hDeadCover := plane461GenDeadAll
  hPlaneLeSource := plane461GenSourceAll
  hPlaneLeDead := plane461GenDeadSourceAll
  hIndicator := plane461GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
