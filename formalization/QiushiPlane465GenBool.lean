import QiushiPlane465GenSectionAll
import QiushiPlane465GenDeadAll
import QiushiPlane465GenSourceAll
import QiushiPlane465GenDeadSourceAll
import QiushiPlane465GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane465GenBool : PlaneExtBool plane465GenConfig where
  hSectionCoset := plane465GenSectionAll
  hDeadCover := plane465GenDeadAll
  hPlaneLeSource := plane465GenSourceAll
  hPlaneLeDead := plane465GenDeadSourceAll
  hIndicator := plane465GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
