import QiushiPlane298GenSectionAll
import QiushiPlane298GenDeadAll
import QiushiPlane298GenSourceAll
import QiushiPlane298GenDeadSourceAll
import QiushiPlane298GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane298GenBool : PlaneExtBool plane298GenConfig where
  hSectionCoset := plane298GenSectionAll
  hDeadCover := plane298GenDeadAll
  hPlaneLeSource := plane298GenSourceAll
  hPlaneLeDead := plane298GenDeadSourceAll
  hIndicator := plane298GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
