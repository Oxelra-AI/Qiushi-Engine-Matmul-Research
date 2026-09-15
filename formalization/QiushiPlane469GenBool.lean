import QiushiPlane469GenSectionAll
import QiushiPlane469GenDeadAll
import QiushiPlane469GenSourceAll
import QiushiPlane469GenDeadSourceAll
import QiushiPlane469GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane469GenBool : PlaneExtBool plane469GenConfig where
  hSectionCoset := plane469GenSectionAll
  hDeadCover := plane469GenDeadAll
  hPlaneLeSource := plane469GenSourceAll
  hPlaneLeDead := plane469GenDeadSourceAll
  hIndicator := plane469GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
