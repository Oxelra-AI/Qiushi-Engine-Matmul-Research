import QiushiPlane463GenSectionAll
import QiushiPlane463GenDeadAll
import QiushiPlane463GenSourceAll
import QiushiPlane463GenDeadSourceAll
import QiushiPlane463GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane463GenBool : PlaneExtBool plane463GenConfig where
  hSectionCoset := plane463GenSectionAll
  hDeadCover := plane463GenDeadAll
  hPlaneLeSource := plane463GenSourceAll
  hPlaneLeDead := plane463GenDeadSourceAll
  hIndicator := plane463GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
