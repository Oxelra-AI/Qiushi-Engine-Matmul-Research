import QiushiPlane464GenSectionAll
import QiushiPlane464GenDeadAll
import QiushiPlane464GenSourceAll
import QiushiPlane464GenDeadSourceAll
import QiushiPlane464GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane464GenBool : PlaneExtBool plane464GenConfig where
  hSectionCoset := plane464GenSectionAll
  hDeadCover := plane464GenDeadAll
  hPlaneLeSource := plane464GenSourceAll
  hPlaneLeDead := plane464GenDeadSourceAll
  hIndicator := plane464GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
