import QiushiPlane485GenSectionAll
import QiushiPlane485GenDeadAll
import QiushiPlane485GenSourceAll
import QiushiPlane485GenDeadSourceAll
import QiushiPlane485GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane485GenBool : PlaneExtBool plane485GenConfig where
  hSectionCoset := plane485GenSectionAll
  hDeadCover := plane485GenDeadAll
  hPlaneLeSource := plane485GenSourceAll
  hPlaneLeDead := plane485GenDeadSourceAll
  hIndicator := plane485GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
