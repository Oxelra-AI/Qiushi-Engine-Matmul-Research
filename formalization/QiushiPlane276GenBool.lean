import QiushiPlane276GenSectionAll
import QiushiPlane276GenDeadAll
import QiushiPlane276GenSourceAll
import QiushiPlane276GenDeadSourceAll
import QiushiPlane276GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane276GenBool : PlaneExtBool plane276GenConfig where
  hSectionCoset := plane276GenSectionAll
  hDeadCover := plane276GenDeadAll
  hPlaneLeSource := plane276GenSourceAll
  hPlaneLeDead := plane276GenDeadSourceAll
  hIndicator := plane276GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
