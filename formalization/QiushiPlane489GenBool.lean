import QiushiPlane489GenSectionAll
import QiushiPlane489GenDeadAll
import QiushiPlane489GenSourceAll
import QiushiPlane489GenDeadSourceAll
import QiushiPlane489GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane489GenBool : PlaneExtBool plane489GenConfig where
  hSectionCoset := plane489GenSectionAll
  hDeadCover := plane489GenDeadAll
  hPlaneLeSource := plane489GenSourceAll
  hPlaneLeDead := plane489GenDeadSourceAll
  hIndicator := plane489GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
