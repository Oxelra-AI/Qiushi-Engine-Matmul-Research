import QiushiPlane458GenSectionAll
import QiushiPlane458GenDeadAll
import QiushiPlane458GenSourceAll
import QiushiPlane458GenDeadSourceAll
import QiushiPlane458GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane458GenBool : PlaneExtBool plane458GenConfig where
  hSectionCoset := plane458GenSectionAll
  hDeadCover := plane458GenDeadAll
  hPlaneLeSource := plane458GenSourceAll
  hPlaneLeDead := plane458GenDeadSourceAll
  hIndicator := plane458GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
