import QiushiPlane278GenSectionAll
import QiushiPlane278GenDeadAll
import QiushiPlane278GenSourceAll
import QiushiPlane278GenDeadSourceAll
import QiushiPlane278GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane278GenBool : PlaneExtBool plane278GenConfig where
  hSectionCoset := plane278GenSectionAll
  hDeadCover := plane278GenDeadAll
  hPlaneLeSource := plane278GenSourceAll
  hPlaneLeDead := plane278GenDeadSourceAll
  hIndicator := plane278GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
