import QiushiPlane470GenSectionAll
import QiushiPlane470GenDeadAll
import QiushiPlane470GenSourceAll
import QiushiPlane470GenDeadSourceAll
import QiushiPlane470GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane470GenBool : PlaneExtBool plane470GenConfig where
  hSectionCoset := plane470GenSectionAll
  hDeadCover := plane470GenDeadAll
  hPlaneLeSource := plane470GenSourceAll
  hPlaneLeDead := plane470GenDeadSourceAll
  hIndicator := plane470GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
