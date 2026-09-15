import QiushiPlane292GenSectionAll
import QiushiPlane292GenDeadAll
import QiushiPlane292GenSourceAll
import QiushiPlane292GenDeadSourceAll
import QiushiPlane292GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane292GenBool : PlaneExtBool plane292GenConfig where
  hSectionCoset := plane292GenSectionAll
  hDeadCover := plane292GenDeadAll
  hPlaneLeSource := plane292GenSourceAll
  hPlaneLeDead := plane292GenDeadSourceAll
  hIndicator := plane292GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
