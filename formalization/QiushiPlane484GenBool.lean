import QiushiPlane484GenSectionAll
import QiushiPlane484GenDeadAll
import QiushiPlane484GenSourceAll
import QiushiPlane484GenDeadSourceAll
import QiushiPlane484GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane484GenBool : PlaneExtBool plane484GenConfig where
  hSectionCoset := plane484GenSectionAll
  hDeadCover := plane484GenDeadAll
  hPlaneLeSource := plane484GenSourceAll
  hPlaneLeDead := plane484GenDeadSourceAll
  hIndicator := plane484GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
