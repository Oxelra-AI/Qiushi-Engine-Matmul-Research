import QiushiPlane448GenSectionAll
import QiushiPlane448GenDeadAll
import QiushiPlane448GenSourceAll
import QiushiPlane448GenDeadSourceAll
import QiushiPlane448GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane448GenBool : PlaneExtBool plane448GenConfig where
  hSectionCoset := plane448GenSectionAll
  hDeadCover := plane448GenDeadAll
  hPlaneLeSource := plane448GenSourceAll
  hPlaneLeDead := plane448GenDeadSourceAll
  hIndicator := plane448GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
