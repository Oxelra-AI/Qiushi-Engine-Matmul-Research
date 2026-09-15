import QiushiPlane427GenSectionAll
import QiushiPlane427GenDeadAll
import QiushiPlane427GenSourceAll
import QiushiPlane427GenDeadSourceAll
import QiushiPlane427GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane427GenBool : PlaneExtBool plane427GenConfig where
  hSectionCoset := plane427GenSectionAll
  hDeadCover := plane427GenDeadAll
  hPlaneLeSource := plane427GenSourceAll
  hPlaneLeDead := plane427GenDeadSourceAll
  hIndicator := plane427GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
