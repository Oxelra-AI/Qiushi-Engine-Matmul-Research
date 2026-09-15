import QiushiPlane473GenSectionAll
import QiushiPlane473GenDeadAll
import QiushiPlane473GenSourceAll
import QiushiPlane473GenDeadSourceAll
import QiushiPlane473GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane473GenBool : PlaneExtBool plane473GenConfig where
  hSectionCoset := plane473GenSectionAll
  hDeadCover := plane473GenDeadAll
  hPlaneLeSource := plane473GenSourceAll
  hPlaneLeDead := plane473GenDeadSourceAll
  hIndicator := plane473GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
