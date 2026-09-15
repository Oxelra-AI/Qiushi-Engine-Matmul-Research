import QiushiPlane453GenSectionAll
import QiushiPlane453GenDeadAll
import QiushiPlane453GenSourceAll
import QiushiPlane453GenDeadSourceAll
import QiushiPlane453GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane453GenBool : PlaneExtBool plane453GenConfig where
  hSectionCoset := plane453GenSectionAll
  hDeadCover := plane453GenDeadAll
  hPlaneLeSource := plane453GenSourceAll
  hPlaneLeDead := plane453GenDeadSourceAll
  hIndicator := plane453GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
