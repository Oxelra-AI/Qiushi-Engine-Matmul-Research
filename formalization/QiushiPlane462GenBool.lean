import QiushiPlane462GenSectionAll
import QiushiPlane462GenDeadAll
import QiushiPlane462GenSourceAll
import QiushiPlane462GenDeadSourceAll
import QiushiPlane462GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane462GenBool : PlaneExtBool plane462GenConfig where
  hSectionCoset := plane462GenSectionAll
  hDeadCover := plane462GenDeadAll
  hPlaneLeSource := plane462GenSourceAll
  hPlaneLeDead := plane462GenDeadSourceAll
  hIndicator := plane462GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
