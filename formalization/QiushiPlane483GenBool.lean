import QiushiPlane483GenSectionAll
import QiushiPlane483GenDeadAll
import QiushiPlane483GenSourceAll
import QiushiPlane483GenDeadSourceAll
import QiushiPlane483GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane483GenBool : PlaneExtBool plane483GenConfig where
  hSectionCoset := plane483GenSectionAll
  hDeadCover := plane483GenDeadAll
  hPlaneLeSource := plane483GenSourceAll
  hPlaneLeDead := plane483GenDeadSourceAll
  hIndicator := plane483GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
