import QiushiPlane475GenSectionAll
import QiushiPlane475GenDeadAll
import QiushiPlane475GenSourceAll
import QiushiPlane475GenDeadSourceAll
import QiushiPlane475GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane475GenBool : PlaneExtBool plane475GenConfig where
  hSectionCoset := plane475GenSectionAll
  hDeadCover := plane475GenDeadAll
  hPlaneLeSource := plane475GenSourceAll
  hPlaneLeDead := plane475GenDeadSourceAll
  hIndicator := plane475GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
