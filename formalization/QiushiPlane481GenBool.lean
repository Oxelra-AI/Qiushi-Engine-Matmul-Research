import QiushiPlane481GenSectionAll
import QiushiPlane481GenDeadAll
import QiushiPlane481GenSourceAll
import QiushiPlane481GenDeadSourceAll
import QiushiPlane481GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane481GenBool : PlaneExtBool plane481GenConfig where
  hSectionCoset := plane481GenSectionAll
  hDeadCover := plane481GenDeadAll
  hPlaneLeSource := plane481GenSourceAll
  hPlaneLeDead := plane481GenDeadSourceAll
  hIndicator := plane481GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
