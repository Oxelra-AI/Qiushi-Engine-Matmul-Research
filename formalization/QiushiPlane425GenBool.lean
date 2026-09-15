import QiushiPlane425GenSectionAll
import QiushiPlane425GenDeadAll
import QiushiPlane425GenSourceAll
import QiushiPlane425GenDeadSourceAll
import QiushiPlane425GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane425GenBool : PlaneExtBool plane425GenConfig where
  hSectionCoset := plane425GenSectionAll
  hDeadCover := plane425GenDeadAll
  hPlaneLeSource := plane425GenSourceAll
  hPlaneLeDead := plane425GenDeadSourceAll
  hIndicator := plane425GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
