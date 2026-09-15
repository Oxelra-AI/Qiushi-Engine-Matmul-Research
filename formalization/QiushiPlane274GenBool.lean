import QiushiPlane274GenSectionAll
import QiushiPlane274GenDeadAll
import QiushiPlane274GenSourceAll
import QiushiPlane274GenDeadSourceAll
import QiushiPlane274GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane274GenBool : PlaneExtBool plane274GenConfig where
  hSectionCoset := plane274GenSectionAll
  hDeadCover := plane274GenDeadAll
  hPlaneLeSource := plane274GenSourceAll
  hPlaneLeDead := plane274GenDeadSourceAll
  hIndicator := plane274GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
