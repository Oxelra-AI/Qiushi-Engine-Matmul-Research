import QiushiPlane269GenSectionAll
import QiushiPlane269GenDeadAll
import QiushiPlane269GenSourceAll
import QiushiPlane269GenDeadSourceAll
import QiushiPlane269GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane269GenBool : PlaneExtBool plane269GenConfig where
  hSectionCoset := plane269GenSectionAll
  hDeadCover := plane269GenDeadAll
  hPlaneLeSource := plane269GenSourceAll
  hPlaneLeDead := plane269GenDeadSourceAll
  hIndicator := plane269GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
