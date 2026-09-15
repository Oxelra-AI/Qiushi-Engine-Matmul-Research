import QiushiPlane295GenSectionAll
import QiushiPlane295GenDeadAll
import QiushiPlane295GenSourceAll
import QiushiPlane295GenDeadSourceAll
import QiushiPlane295GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane295GenBool : PlaneExtBool plane295GenConfig where
  hSectionCoset := plane295GenSectionAll
  hDeadCover := plane295GenDeadAll
  hPlaneLeSource := plane295GenSourceAll
  hPlaneLeDead := plane295GenDeadSourceAll
  hIndicator := plane295GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
