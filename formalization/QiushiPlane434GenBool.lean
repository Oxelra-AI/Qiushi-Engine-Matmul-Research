import QiushiPlane434GenSectionAll
import QiushiPlane434GenDeadAll
import QiushiPlane434GenSourceAll
import QiushiPlane434GenDeadSourceAll
import QiushiPlane434GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane434GenBool : PlaneExtBool plane434GenConfig where
  hSectionCoset := plane434GenSectionAll
  hDeadCover := plane434GenDeadAll
  hPlaneLeSource := plane434GenSourceAll
  hPlaneLeDead := plane434GenDeadSourceAll
  hIndicator := plane434GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
