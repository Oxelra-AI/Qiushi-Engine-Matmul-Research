import QiushiPlane255GenSectionAll
import QiushiPlane255GenDeadAll
import QiushiPlane255GenSourceAll
import QiushiPlane255GenDeadSourceAll
import QiushiPlane255GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane255GenBool : PlaneExtBool plane255GenConfig where
  hSectionCoset := plane255GenSectionAll
  hDeadCover := plane255GenDeadAll
  hPlaneLeSource := plane255GenSourceAll
  hPlaneLeDead := plane255GenDeadSourceAll
  hIndicator := plane255GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
