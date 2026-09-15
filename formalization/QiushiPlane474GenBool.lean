import QiushiPlane474GenSectionAll
import QiushiPlane474GenDeadAll
import QiushiPlane474GenSourceAll
import QiushiPlane474GenDeadSourceAll
import QiushiPlane474GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane474GenBool : PlaneExtBool plane474GenConfig where
  hSectionCoset := plane474GenSectionAll
  hDeadCover := plane474GenDeadAll
  hPlaneLeSource := plane474GenSourceAll
  hPlaneLeDead := plane474GenDeadSourceAll
  hIndicator := plane474GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
