import QiushiPlane490GenSectionAll
import QiushiPlane490GenDeadAll
import QiushiPlane490GenSourceAll
import QiushiPlane490GenDeadSourceAll
import QiushiPlane490GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane490GenBool : PlaneExtBool plane490GenConfig where
  hSectionCoset := plane490GenSectionAll
  hDeadCover := plane490GenDeadAll
  hPlaneLeSource := plane490GenSourceAll
  hPlaneLeDead := plane490GenDeadSourceAll
  hIndicator := plane490GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
