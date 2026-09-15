import QiushiPlane428GenSectionAll
import QiushiPlane428GenDeadAll
import QiushiPlane428GenSourceAll
import QiushiPlane428GenDeadSourceAll
import QiushiPlane428GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane428GenBool : PlaneExtBool plane428GenConfig where
  hSectionCoset := plane428GenSectionAll
  hDeadCover := plane428GenDeadAll
  hPlaneLeSource := plane428GenSourceAll
  hPlaneLeDead := plane428GenDeadSourceAll
  hIndicator := plane428GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
