import QiushiPlane488GenSectionAll
import QiushiPlane488GenDeadAll
import QiushiPlane488GenSourceAll
import QiushiPlane488GenDeadSourceAll
import QiushiPlane488GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane488GenBool : PlaneExtBool plane488GenConfig where
  hSectionCoset := plane488GenSectionAll
  hDeadCover := plane488GenDeadAll
  hPlaneLeSource := plane488GenSourceAll
  hPlaneLeDead := plane488GenDeadSourceAll
  hIndicator := plane488GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
