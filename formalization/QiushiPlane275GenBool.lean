import QiushiPlane275GenSectionAll
import QiushiPlane275GenDeadAll
import QiushiPlane275GenSourceAll
import QiushiPlane275GenDeadSourceAll
import QiushiPlane275GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane275GenBool : PlaneExtBool plane275GenConfig where
  hSectionCoset := plane275GenSectionAll
  hDeadCover := plane275GenDeadAll
  hPlaneLeSource := plane275GenSourceAll
  hPlaneLeDead := plane275GenDeadSourceAll
  hIndicator := plane275GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
