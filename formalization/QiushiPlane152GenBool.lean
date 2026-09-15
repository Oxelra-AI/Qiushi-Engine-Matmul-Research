import QiushiPlane152GenSectionAll
import QiushiPlane152GenDeadAll
import QiushiPlane152GenSourceAll
import QiushiPlane152GenDeadSourceAll
import QiushiPlane152GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane152GenBool : PlaneExtBool plane152GenConfig where
  hSectionCoset := plane152GenSectionAll
  hDeadCover := plane152GenDeadAll
  hPlaneLeSource := plane152GenSourceAll
  hPlaneLeDead := plane152GenDeadSourceAll
  hIndicator := plane152GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
