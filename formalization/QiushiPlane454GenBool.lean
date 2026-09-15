import QiushiPlane454GenSectionAll
import QiushiPlane454GenDeadAll
import QiushiPlane454GenSourceAll
import QiushiPlane454GenDeadSourceAll
import QiushiPlane454GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane454GenBool : PlaneExtBool plane454GenConfig where
  hSectionCoset := plane454GenSectionAll
  hDeadCover := plane454GenDeadAll
  hPlaneLeSource := plane454GenSourceAll
  hPlaneLeDead := plane454GenDeadSourceAll
  hIndicator := plane454GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
