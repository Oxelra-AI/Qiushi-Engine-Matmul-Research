import QiushiPlane456GenSectionAll
import QiushiPlane456GenDeadAll
import QiushiPlane456GenSourceAll
import QiushiPlane456GenDeadSourceAll
import QiushiPlane456GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane456GenBool : PlaneExtBool plane456GenConfig where
  hSectionCoset := plane456GenSectionAll
  hDeadCover := plane456GenDeadAll
  hPlaneLeSource := plane456GenSourceAll
  hPlaneLeDead := plane456GenDeadSourceAll
  hIndicator := plane456GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
