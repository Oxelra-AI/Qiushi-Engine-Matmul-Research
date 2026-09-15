import QiushiPlane336GenSectionAll
import QiushiPlane336GenDeadAll
import QiushiPlane336GenSourceAll
import QiushiPlane336GenDeadSourceAll
import QiushiPlane336GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane336GenBool : PlaneExtBool plane336GenConfig where
  hSectionCoset := plane336GenSectionAll
  hDeadCover := plane336GenDeadAll
  hPlaneLeSource := plane336GenSourceAll
  hPlaneLeDead := plane336GenDeadSourceAll
  hIndicator := plane336GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
